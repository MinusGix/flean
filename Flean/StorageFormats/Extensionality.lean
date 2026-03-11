import Flean.StorageFormats.FromFp
import Flean.StorageFormats.Conversion
import Flean.StorageFormats.FromFpCorrect
import Flean.StorageFormats.RoundRNEVerify

/-!
# StorageFp Extensionality and General Round-Trip

Proves bitvector extensionality for `StorageFp` and the general structural round-trip:
`fromFiniteFp (toFiniteFp v) = v` for all finite values in any signed StorageFormat.

This subsumes the per-format exhaustive `decide` proofs in `RoundTrip.lean`.
-/

namespace StorageFp
variable {f : StorageFormat}

/-! ## Bitvector Extensionality

Decompose a `StorageFp`'s bits into sign, exponent, and mantissa fields,
then prove two values are equal iff their fields match.
-/

theorem man_eq_bits_mod (v : StorageFp f) : v.man = v.bits.toNat % 2 ^ f.manBits := by
  unfold man; simp only [BitVec.toNat_and]
  rw [zeroExtend_allOnes_toNat f.manBits f.bitSize (manBits_le_bitSize f)]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (dvd_refl _)]

theorem exp_eq_bits_div_mod (v : StorageFp f) :
    v.exp = (v.bits.toNat / 2 ^ f.manBits) % 2 ^ f.expBits := by
  unfold exp; simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [zeroExtend_allOnes_toNat f.expBits f.bitSize (expBits_le_bitSize f)]
  rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_mod_of_dvd _ (dvd_refl _)

private theorem testBit_of_div_01 {n k : ℕ} (h : n / 2 ^ k = 0 ∨ n / 2 ^ k = 1) :
    n.testBit k = decide (n / 2 ^ k = 1) := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; rcases h with h | h <;> simp [h]

theorem sign_eq_bits_div (v : StorageFp f) (hsigned : f.hasSigned = true) :
    (if v.sign then 1 else 0) = v.bits.toNat / 2 ^ (f.expBits + f.manBits) := by
  have hbs : f.bitSize = 1 + f.expBits + f.manBits := by
    unfold StorageFormat.bitSize; rw [hsigned]; simp
  have hbs_sub : f.bitSize - 1 = f.expBits + f.manBits := by omega
  set d := v.bits.toNat / 2 ^ (f.expBits + f.manBits)
  have hdiv_lt : d < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      show 2 * 2 ^ (f.expBits + f.manBits) = 2 ^ (1 + f.expBits + f.manBits) from by ring]
    exact hbs ▸ v.bits.isLt
  have hdiv_01 : d = 0 ∨ d = 1 := by interval_cases d <;> simp
  unfold StorageFp.sign; simp only [hsigned, ite_true]
  show (if v.bits.getMsbD 0 then (1 : ℕ) else 0) = d
  have : v.bits.getMsbD 0 = decide (d = 1) := by
    simp only [BitVec.getMsbD, BitVec.getLsbD, hbs_sub, f.bitSize_pos, decide_true, Bool.true_and]
    exact testBit_of_div_01 hdiv_01
  rw [this]; rcases hdiv_01 with h | h <;> simp [h]

private theorem nat_field_decompose (n mB eB : ℕ) :
    n = n / 2 ^ (eB + mB) * 2 ^ (eB + mB) +
      (n / 2 ^ mB) % 2 ^ eB * 2 ^ mB + n % 2 ^ mB := by
  have h1 := (Nat.div_add_mod n (2 ^ mB)).symm
  have h2 := (Nat.div_add_mod (n / 2 ^ mB) (2 ^ eB)).symm
  rw [Nat.div_div_eq_div_mul, show 2 ^ mB * 2 ^ eB = 2 ^ (eB + mB) from by
    rw [← Nat.pow_add]; ring] at h2
  set q := n / 2 ^ mB; set r := n % 2 ^ mB
  set Q := n / 2 ^ (eB + mB); set R := q % 2 ^ eB
  have : 2 ^ mB * q = Q * 2 ^ (eB + mB) + R * 2 ^ mB := by
    calc 2 ^ mB * q = 2 ^ mB * (2 ^ eB * Q + R) := by rw [h2]
      _ = Q * (2 ^ mB * 2 ^ eB) + R * 2 ^ mB := by ring
      _ = Q * 2 ^ (eB + mB) + R * 2 ^ mB := by
          rw [show 2 ^ mB * 2 ^ eB = 2 ^ (eB + mB) from by rw [← Nat.pow_add]; ring]
  linarith

theorem bits_toNat_decompose (v : StorageFp f) (hsigned : f.hasSigned = true) :
    v.bits.toNat = (if v.sign then 1 else 0) * 2 ^ (f.expBits + f.manBits) +
      v.exp * 2 ^ f.manBits + v.man := by
  rw [man_eq_bits_mod, exp_eq_bits_div_mod, sign_eq_bits_div v hsigned]
  exact nat_field_decompose v.bits.toNat f.manBits f.expBits

theorem ext_fields (v w : StorageFp f) (hsigned : f.hasSigned = true)
    (hs : v.sign = w.sign) (he : v.exp = w.exp) (hm : v.man = w.man) : v = w := by
  have hv := bits_toNat_decompose v hsigned
  have hw := bits_toNat_decompose w hsigned
  have : v.bits.toNat = w.bits.toNat := by rw [hv, hw, hs, he, hm]
  exact congrArg (⟨·⟩ : BitVec f.bitSize → StorageFp f) (BitVec.eq_of_toNat_eq this)

theorem eq_ofFields (v : StorageFp f) (hsigned : f.hasSigned = true) :
    v = ofFields f v.sign v.exp v.man := by
  apply ext_fields v _ hsigned
  · exact (ofFields_sign v.sign v.exp v.man v.man_lt v.exp_lt hsigned).symm
  · exact (ofFields_exp v.sign v.exp v.man v.man_lt v.exp_lt).symm
  · exact (ofFields_man v.sign v.exp v.man v.man_lt v.exp_lt).symm

/-! ## Zero-value helpers -/

private theorem zero_eq_of_fields (v : StorageFp f) (hsigned : f.hasSigned = true)
    (hsign : v.sign = false) (hexp : v.exp = 0) (hman : v.man = 0) :
    zero f = v := by
  apply congrArg StorageFp.mk
  apply BitVec.eq_of_toNat_eq
  change 0 = v.bits.toNat
  have hd := bits_toNat_decompose v hsigned
  simp only [hsign, hexp, hman, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hd
  omega

private theorem negZero_eq_of_fields (v : StorageFp f) (hsigned : f.hasSigned = true)
    (hsign : v.sign = true) (hexp : v.exp = 0) (hman : v.man = 0) :
    negZero f = v := by
  apply congrArg StorageFp.mk
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat f.bitSize (2 ^ (f.bitSize - 1))).toNat = v.bits.toNat
  simp only [BitVec.toNat_ofNat]
  have hd := bits_toNat_decompose v hsigned
  simp only [hsign, hexp, hman, ite_true, one_mul, zero_mul, add_zero] at hd
  have hbs : f.bitSize - 1 = f.expBits + f.manBits := by
    unfold StorageFormat.bitSize; simp [hsigned]; omega
  conv_lhs => rw [hbs]
  rw [Nat.mod_eq_of_lt]
  · omega
  · have hbs2 : f.bitSize = f.expBits + f.manBits + 1 := by
      unfold StorageFormat.bitSize; simp [hsigned]; omega
    rw [hbs2]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## roundSigCore exactness -/

/-- When e_ulp = e_base (shift = 0) and no overflow, roundSigCore returns the input unchanged. -/
private theorem roundSigCore_exact
    (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (prec : ℕ) (min_exp max_exp : ℤ)
    (shouldRoundUp : Bool → ℕ → ℕ → ℕ → Bool)
    (he_ulp : max (e_base + ↑(Nat.log2 mag + 1) - ↑prec) (min_exp - ↑prec + 1) = e_base)
    (hno_overflow : e_base + ↑prec - 1 ≤ max_exp) :
    roundSigCore sign mag e_base prec min_exp max_exp shouldRoundUp = (mag, e_base, false) := by
  unfold roundSigCore
  simp only [he_ulp, sub_self, le_refl, ↓reduceIte, neg_zero, Int.toNat_zero, pow_zero, mul_one,
    show ¬(e_base + ↑prec - 1 > max_exp) from by omega]

/-! ## Helper lemmas -/

private theorem log2_normal_sig (mB man : ℕ) (hman : man < 2 ^ mB) :
    Nat.log2 (2 ^ mB + man) = mB := by
  have hne : 2 ^ mB + man ≠ 0 := by omega
  have h1 : Nat.log2 (2 ^ mB + man) < mB + 1 := (Nat.log2_lt hne).mpr (by omega)
  have h2 : mB ≤ Nat.log2 (2 ^ mB + man) := by
    by_contra h; push_neg at h
    exact absurd ((Nat.log2_lt hne).mp (by omega : Nat.log2 (2 ^ mB + man) < mB)) (by omega)
  omega

private theorem log2_subnormal_sig (mB man : ℕ) (hman_pos : 0 < man) (hman_lt : man < 2 ^ mB) :
    Nat.log2 man + 1 ≤ mB := by
  have := (Nat.log2_lt (by omega : man ≠ 0)).mpr hman_lt; omega

private theorem finite_man_le_maxManFieldAtMaxExp' (v : StorageFp f) (hfin : v.isFinite)
    (h_nan_valid : f.hasNaN → 0 < f.nanCount) :
    v.man ≤ f.maxManFieldAtMaxExp ∨ v.exp < f.maxExpField := by
  by_cases hexp : v.exp < f.maxExpField
  · exact Or.inr hexp
  · push_neg at hexp; left
    unfold StorageFormat.maxManFieldAtMaxExp
    split_ifs with h1 h2
    · obtain ⟨hnan, _, hmax_eq⟩ := h1
      have hexp_eq : v.exp = 2 ^ f.expBits - 1 := by have := v.exp_lt; rw [hmax_eq] at hexp; omega
      have := hfin.1; unfold isNaN at this; push_neg at this
      have := this hnan hexp_eq; simp only [h2, ite_true] at this
      have := v.man_lt; omega
    · obtain ⟨hnan, _, hmax_eq⟩ := h1
      have hexp_eq : v.exp = 2 ^ f.expBits - 1 := by have := v.exp_lt; rw [hmax_eq] at hexp; omega
      have := hfin.1; unfold isNaN at this; push_neg at this
      have := this hnan hexp_eq
      have hnc := h_nan_valid hnan
      simp only [h2, ite_false, show 0 < f.nanCount from hnc, ite_true] at this
      push_neg at this; omega
    · have := v.man_lt; omega

/-! ## General Round-Trip Theorem -/

/-- The general structural round-trip:
    `fromFiniteFp (toFiniteFp v) = v` for all finite values in any signed StorageFormat.
    Requires `hasNaN → nanCount > 0` to exclude a degenerate format configuration. -/
theorem roundtrip_general
    (f : StorageFormat)
    (h_prec : f.manBits ≥ 1) (h_bias : f.bias ≥ 1) (h_exp : f.maxExpField > f.bias)
    (hsigned : f.hasSigned = true)
    (h_nan_valid : f.hasNaN → 0 < f.nanCount)
    (v : StorageFp f) (hfin : v.isFinite) :
    @fromFiniteFp (f.toFloatFormat h_prec h_bias h_exp) f .saturate
      (v.toFiniteFp h_prec h_bias h_exp hfin) = v := by
  letI ff := f.toFloatFormat h_prec h_bias h_exp
  set fp := v.toFiniteFp h_prec h_bias h_exp hfin
  unfold fromFiniteFp
  show fromFp f .saturate (Fp.finite fp) = v
  have hfp_s : fp.s = v.sign := rfl
  have hfp_e : fp.e = v.unbiasedExp := rfl
  have hfp_m : fp.m = v.effectiveSignificand := rfl
  have hprec_eq : ff.prec = (f.manBits : ℤ) + 1 := rfl
  by_cases hm_zero : v.effectiveSignificand = 0
  · -- ═══ ZERO CASE ═══
    have hman0 : v.man = 0 := by
      unfold effectiveSignificand at hm_zero; split_ifs at hm_zero with h
      · exact hm_zero
      · exfalso; have := Nat.two_pow_pos f.manBits; omega
    have hexp0 : v.isExpZero := by
      unfold effectiveSignificand at hm_zero; split_ifs at hm_zero with h
      · exact h
      · exfalso; have := Nat.two_pow_pos f.manBits; omega
    have hfp_m0 : fp.m = 0 := by rw [hfp_m]; exact hm_zero
    unfold fromFp; simp only [hfp_m0, ↓reduceIte, hfp_s]
    rcases Bool.eq_false_or_eq_true v.sign with hsign | hsign <;> simp only [hsign, ↓reduceIte]
    · exact negZero_eq_of_fields v hsigned hsign hexp0 hman0
    · exact zero_eq_of_fields v hsigned hsign hexp0 hman0
  · -- ═══ NONZERO CASE ═══
    have hfp_m_ne : fp.m ≠ 0 := by rw [hfp_m]; exact hm_zero
    unfold fromFp; simp only [show ¬(fp.m = 0) from hfp_m_ne, ↓reduceIte]
    -- Show roundSigCore is exact: e_ulp = e_base
    have he_ulp_eq : max (fp.e - ff.prec + 1 + ↑(Nat.log2 fp.m + 1) - ↑(f.manBits + 1))
        (1 - (f.bias : ℤ) - ↑(f.manBits + 1) + 1) = fp.e - ff.prec + 1 := by
      rw [hfp_m, hfp_e, hprec_eq]
      by_cases hexp0 : v.isExpZero
      · have hue : v.unbiasedExp = 1 - (f.bias : ℤ) := by simp [unbiasedExp, hexp0]
        have hes : v.effectiveSignificand = v.man := by simp [effectiveSignificand, hexp0]
        rw [hue, hes]
        have hman_pos : 0 < v.man := by rw [← hes]; exact Nat.pos_of_ne_zero hm_zero
        have hlog_le := log2_subnormal_sig f.manBits v.man hman_pos v.man_lt
        simp only [max_def]; split_ifs with h <;> push_cast <;> omega
      · have hue : v.unbiasedExp = (v.exp : ℤ) - (f.bias : ℤ) := by simp [unbiasedExp, hexp0]
        have hes : v.effectiveSignificand = 2 ^ f.manBits + v.man := by
          simp [effectiveSignificand, hexp0]
        rw [hue, hes, log2_normal_sig f.manBits v.man v.man_lt]
        have hexp_pos : 0 < v.exp := by unfold isExpZero at hexp0; omega
        simp only [max_def]; split_ifs with h <;> push_cast <;> omega
    -- No overflow
    have hno_overflow : fp.e - ff.prec + 1 + ↑(f.manBits + 1) - 1 ≤
        (f.maxExpField : ℤ) - (f.bias : ℤ) := by
      rw [hfp_e, hprec_eq]
      by_cases hexp0 : v.isExpZero
      · rw [show v.unbiasedExp = 1 - (f.bias : ℤ) from by simp [unbiasedExp, hexp0]]
        push_cast; omega
      · rw [show v.unbiasedExp = (v.exp : ℤ) - (f.bias : ℤ) from by simp [unbiasedExp, hexp0]]
        have := v.exp_le_maxExpField_of_isFinite hfin
        push_cast; omega
    -- Apply roundSigCore_exact
    have hrc := roundSigCore_exact fp.s fp.m (fp.e - ff.prec + 1) (f.manBits + 1)
      (1 - (f.bias : ℤ)) ((f.maxExpField : ℤ) - (f.bias : ℤ)) rneRoundUp
      he_ulp_eq hno_overflow
    simp only [hrc]
    simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩, ite_false]
    rw [hfp_s, hfp_m, show fp.e - ff.prec + 1 = v.unbiasedExp - (f.manBits : ℤ) from by
      rw [hfp_e, hprec_eq]; ring]
    -- Case split: normal vs subnormal for encodeRounded
    by_cases hexp0 : v.isExpZero
    · -- Subnormal encoding
      have hes : v.effectiveSignificand = v.man := by simp [effectiveSignificand, hexp0]
      have hue : v.unbiasedExp = 1 - (f.bias : ℤ) := by simp [unbiasedExp, hexp0]
      rw [hes, hue]
      have hman_ne : v.man ≠ 0 := by rw [← hes]; exact hm_zero
      unfold encodeRounded
      simp only [show ¬(v.man = 0) from hman_ne, show v.man < 2 ^ f.manBits from v.man_lt,
        ↓reduceIte]
      rw [← show v.exp = 0 from hexp0]
      exact (eq_ofFields v hsigned).symm
    · -- Normal encoding
      have hes : v.effectiveSignificand = 2 ^ f.manBits + v.man := by
        simp [effectiveSignificand, hexp0]
      have hue : v.unbiasedExp = (v.exp : ℤ) - (f.bias : ℤ) := by simp [unbiasedExp, hexp0]
      rw [hes, hue]
      unfold encodeRounded
      simp only [show ¬(2 ^ f.manBits + v.man = 0) from by
          have := Nat.two_pow_pos f.manBits; omega,
        show ¬(2 ^ f.manBits + v.man < 2 ^ f.manBits) from by omega, ↓reduceIte]
      have hexp_field : (((v.exp : ℤ) - (f.bias : ℤ) - (f.manBits : ℤ)) + (f.manBits : ℤ) +
          (f.bias : ℤ)).toNat = v.exp := by omega
      have hman_field : 2 ^ f.manBits + v.man - 2 ^ f.manBits = v.man := by omega
      simp only [hexp_field, hman_field]
      -- NaN exclusion
      have hnan_check := finite_man_le_maxManFieldAtMaxExp' v hfin h_nan_valid
      split_ifs with hcond
      · exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hnan_check with h | h
        · exact absurd hcond.2 (by omega)
        · exact absurd hcond.1 (by omega)
      · exact (eq_ofFields v hsigned).symm

end StorageFp
