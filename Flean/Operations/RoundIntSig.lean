import Flean.Defs
import Flean.CommonConstants
import Flean.Rounding.ModeClass
import Flean.Rounding.OddInterval

/-! # RoundIntSig: Integer Significand Rounding Primitive

Typeclass-driven rounding primitive `roundIntSigM` for exact values represented as
`±mag * 2^e_base`.

`roundIntSigM` uses execution hooks from `RModeExec` for tie-breaking and overflow
handling, while semantic correctness is tracked separately by `RoundIntSigMSound`.
-/

section RoundIntSig

variable [FloatFormat]

-- Helper: if a < 2^b then a * 2^c < 2^(b + c)
omit [FloatFormat] in
private theorem nat_mul_pow2_lt {a b c : ℕ} (h : a < 2^b) : a * 2^c < 2^(b + c) := by
  rw [Nat.pow_add]
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos c)).mpr h

-- Helper: if bits + extra ≤ prec then mag*2^extra fits in precision bits.
private theorem exact_branch_m_bound {mag bits_nat neg_shift_nat : ℕ}
    (hmag : mag < 2^bits_nat) (hsum : bits_nat + neg_shift_nat ≤ FloatFormat.prec.toNat) :
    mag * 2^neg_shift_nat < 2^FloatFormat.prec.toNat := by
  calc mag * 2^neg_shift_nat < 2^(bits_nat + neg_shift_nat) := nat_mul_pow2_lt hmag
    _ ≤ 2^FloatFormat.prec.toNat := Nat.pow_le_pow_right (by norm_num) hsum

/-- Round an integer significand using contextual execution hooks. -/
def roundIntSigM [RModeExec]
    (sign : Bool) (mag : ℕ) (e_base : ℤ) : Fp :=
  if hmag : mag = 0 then
    Fp.finite (if sign then -0 else 0)
  else
    let bits : ℤ := (Nat.log2 mag + 1 : ℕ)
    let e_ulp_normal := e_base + bits - FloatFormat.prec
    let e_ulp_subnormal := FloatFormat.min_exp - FloatFormat.prec + 1
    let e_ulp := max e_ulp_normal e_ulp_subnormal
    let shift := e_ulp - e_base
    if h_exact : shift ≤ 0 then
      let m := mag * 2^(-shift).toNat
      let e_stored := e_ulp + FloatFormat.prec - 1
      if h_overflow : e_stored > FloatFormat.max_exp then
        RModeExec.handleOverflow sign
      else
        Fp.finite ⟨sign, e_stored, m, by
          set bits_nat := Nat.log2 mag + 1
          have hmag_lt : mag < 2^bits_nat := Nat.lt_log2_self
          have hsum : bits_nat + (-shift).toNat ≤ FloatFormat.prec.toNat := by
            have hp := FloatFormat.prec_pos
            omega
          have hm_bound : m < 2^FloatFormat.prec.toNat :=
            exact_branch_m_bound hmag_lt hsum
          have he_ge_min : e_stored ≥ FloatFormat.min_exp := by
            have hp := FloatFormat.valid_prec
            omega
          have he_le_max : e_stored ≤ FloatFormat.max_exp := by omega
          have h4 : isNormal m ∨ isSubnormal e_stored m := by
            by_cases hm_normal : 2^(FloatFormat.prec - 1).toNat ≤ m
            · left
              exact ⟨hm_normal, hm_bound⟩
            · right
              push_neg at hm_normal
              constructor
              · by_contra h_ne
                have he_ulp_eq : e_ulp = e_base + bits - FloatFormat.prec := by omega
                have hshift_eq : shift = bits - FloatFormat.prec := by omega
                have hneg_shift : (-shift).toNat = (FloatFormat.prec - bits).toNat := by omega
                have hexp_sum : bits_nat - 1 + (-shift).toNat = (FloatFormat.prec - 1).toNat := by
                  have hp := FloatFormat.prec_pos
                  omega
                have hmag_le : 2^(bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
                have : m ≥ 2^(FloatFormat.prec - 1).toNat := by
                  calc 2^(FloatFormat.prec - 1).toNat
                      = 2^(bits_nat - 1 + (-shift).toNat) := by rw [hexp_sum]
                    _ = 2^(bits_nat - 1) * 2^(-shift).toNat := by rw [Nat.pow_add]
                    _ ≤ mag * 2^(-shift).toNat := Nat.mul_le_mul_right _ hmag_le
                omega
              · omega
          exact ⟨he_ge_min, he_le_max, hm_bound, h4⟩⟩
    else
      let shift_nat := shift.toNat
      let divisor := 2^shift_nat
      let q := mag / divisor
      let r := mag % divisor
      let roundUp := RModeExec.shouldRoundUp sign q r shift_nat
      let m_rounded := if roundUp then q + 1 else q
      let carry := m_rounded ≥ 2^FloatFormat.prec.toNat
      let m_final := if carry then m_rounded / 2 else m_rounded
      let e_ulp_final := if carry then e_ulp + 1 else e_ulp
      let e_stored := e_ulp_final + FloatFormat.prec - 1
      if h_overflow2 : e_stored > FloatFormat.max_exp then
        RModeExec.handleOverflow sign
      else
        Fp.finite ⟨sign, e_stored, m_final, by
          set bits_nat := Nat.log2 mag + 1
          have hmag_lt : mag < 2^bits_nat := Nat.lt_log2_self
          have hshift_pos : shift > 0 := by omega
          have hq_bound : q < 2^FloatFormat.prec.toNat := by
            have hsum : FloatFormat.prec.toNat + shift_nat ≥ bits_nat := by
              have hp := FloatFormat.prec_pos
              omega
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift_nat)]
            calc mag < 2^bits_nat := hmag_lt
              _ ≤ 2^(FloatFormat.prec.toNat + shift_nat) :=
                Nat.pow_le_pow_right (by norm_num) hsum
              _ = 2^FloatFormat.prec.toNat * 2^shift_nat := by rw [Nat.pow_add]
          have hm_rounded_le : m_rounded ≤ q + 1 := by
            simp only [m_rounded]
            split_ifs <;> omega
          have hm_rounded_ge_q : m_rounded ≥ q := by
            simp only [m_rounded]
            split_ifs <;> omega
          show IsValidFiniteVal
            ((if carry then e_ulp + 1 else e_ulp) + FloatFormat.prec - 1)
            (if carry then m_rounded / 2 else m_rounded)
          split_ifs with hcarry
          · have hm_rounded_eq : m_rounded = 2^FloatFormat.prec.toNat := by omega
            have hp := FloatFormat.prec_toNat_pos
            have hm_div : m_rounded / 2 = 2^(FloatFormat.prec.toNat - 1) := by
              rw [hm_rounded_eq]
              have : (2 : ℕ)^FloatFormat.prec.toNat = 2 * 2^(FloatFormat.prec.toNat - 1) := by
                conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
              omega
            have hprec_eq : FloatFormat.prec.toNat - 1 = (FloatFormat.prec - 1).toNat :=
              FloatFormat.prec_sub_one_toNat_eq_toNat_sub.symm
            have hm_normal : isNormal (m_rounded / 2) := by
              rw [hm_div, hprec_eq]
              exact isNormal.sig_msb
            have hm_lt : m_rounded / 2 < 2^FloatFormat.prec.toNat := by
              rw [hm_div, hprec_eq]
              exact FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
            have he_ge : e_ulp + 1 + FloatFormat.prec - 1 ≥ FloatFormat.min_exp := by
              have := FloatFormat.valid_prec
              omega
            have he_le : e_ulp + 1 + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by omega
            exact ⟨he_ge, he_le, hm_lt, Or.inl hm_normal⟩
          · have hm_lt : m_rounded < 2^FloatFormat.prec.toNat := by omega
            have he_ge : e_ulp + FloatFormat.prec - 1 ≥ FloatFormat.min_exp := by
              have := FloatFormat.valid_prec
              omega
            have he_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by omega
            have h4 : isNormal m_rounded ∨ isSubnormal (e_ulp + FloatFormat.prec - 1) m_rounded := by
              by_cases hm_normal : 2^(FloatFormat.prec - 1).toNat ≤ m_rounded
              · left
                exact ⟨hm_normal, hm_lt⟩
              · right
                push_neg at hm_normal
                constructor
                · by_contra h_ne
                  have hbits_nat_gt : bits_nat > FloatFormat.prec.toNat := by
                    have := FloatFormat.prec_pos
                    omega
                  have hshift_nat_eq : shift_nat = bits_nat - FloatFormat.prec.toNat := by
                    have := FloatFormat.prec_pos
                    omega
                  have hmag_le : 2^(bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
                  have hq_ge : q ≥ 2^(FloatFormat.prec - 1).toNat := by
                    have hexp_sum : (FloatFormat.prec - 1).toNat +
                        (bits_nat - FloatFormat.prec.toNat) = bits_nat - 1 := by
                      have := FloatFormat.prec_pos
                      omega
                    have hmul_le : 2^(FloatFormat.prec - 1).toNat * 2^shift_nat ≤ mag := by
                      calc 2^(FloatFormat.prec - 1).toNat * 2^shift_nat
                          = 2^(FloatFormat.prec - 1).toNat * 2^(bits_nat - FloatFormat.prec.toNat) := by
                              rw [hshift_nat_eq]
                        _ = 2^((FloatFormat.prec - 1).toNat + (bits_nat - FloatFormat.prec.toNat)) := by
                              rw [Nat.pow_add]
                        _ = 2^(bits_nat - 1) := by rw [hexp_sum]
                        _ ≤ mag := hmag_le
                    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift_nat)).mpr hmul_le
                  omega
                · omega
            exact ⟨he_ge, he_le, hm_lt, h4⟩⟩


/-! ## Correctness Interface -/

section roundIntSig_correctness

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- The real value represented by a signed integer `±mag * 2^e_base`. -/
def intSigVal (sign : Bool) (mag : ℕ) (e_base : ℤ) : R :=
  (if sign then -(mag : R) else (mag : R)) * (2 : R) ^ e_base

omit [FloatFormat] [FloorRing R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Reconstruct signed integer scaling from sign and natAbs for nonzero integers. -/
theorem intSigVal_eq_int_mul {n : ℤ} (hn : n ≠ 0) (e_base : ℤ) :
    intSigVal (R := R) (decide (n < 0)) n.natAbs e_base = (n : R) * (2 : R) ^ e_base := by
  unfold intSigVal
  by_cases hneg : n < 0
  · simp only [hneg, decide_true, ↓reduceIte]
    rw [show (n.natAbs : R) = ((n.natAbs : ℤ) : R) from (Int.cast_natCast n.natAbs).symm,
      Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)]
    push_cast
    ring
  · push_neg at hneg
    have hpos : 0 < n := lt_of_le_of_ne hneg (Ne.symm hn)
    simp only [show ¬(n < 0) from not_lt.mpr (le_of_lt hpos), decide_false,
      Bool.false_eq_true, ↓reduceIte]
    rw [show (n.natAbs : R) = ((n.natAbs : ℤ) : R) from (Int.cast_natCast n.natAbs).symm,
      Int.natAbs_of_nonneg (le_of_lt hpos)]

/-- Semantic contract for `roundIntSigM`: execution policy agrees with `RMode.round`. -/
class RoundIntSigMSound (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [FloatFormat] [RMode R] [RModeExec] : Prop where
  roundIntSigM_correct :
    ∀ (sign : Bool) (mag : ℕ) (e_base : ℤ), mag ≠ 0 →
      roundIntSigM sign mag e_base =
        RMode.round (R := R) (intSigVal (R := R) sign mag e_base)

/-- Generic correctness theorem for `roundIntSigM` under a sound execution policy. -/
theorem roundIntSigM_correct_tc [RMode R] [RModeExec]
    [RoundIntSigMSound R]
    (sign : Bool) (mag : ℕ) (e_base : ℤ) (hmag : mag ≠ 0) :
    roundIntSigM sign mag e_base =
      RMode.round (R := R) (intSigVal (R := R) sign mag e_base) := by
  simpa using (RoundIntSigMSound.roundIntSigM_correct (R := R) sign mag e_base hmag)

end roundIntSig_correctness

/-! ## Sticky-Bit Rounding Interface -/

section sticky_roundIntSig

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Sticky-significand magnitude used by quotient+remainder style algorithms. -/
abbrev stickyMag (q : ℕ) : ℕ := 2 * q + 1

/-- Absolute value of the sticky representative `(2*q+1) * 2^e_base`. -/
abbrev stickyAbs (q : ℕ) (e_base : ℤ) : R := (stickyMag q : R) * (2 : R) ^ e_base

/-- Open interval where sticky rounding is constant:
`(2q * 2^e_base, 2(q+1) * 2^e_base)`. -/
abbrev inStickyInterval (q : ℕ) (e_base : ℤ) (x : R) : Prop :=
  (2 * (q : R)) * (2 : R) ^ e_base < x ∧ x < (2 * ((q : R) + 1)) * (2 : R) ^ e_base

/-- Observable sticky-interval law used by quotient/sqrt sticky-bit proofs. -/
class RModeSticky (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [FloatFormat] [RMode R] : Prop where
  round_eq_on_sticky_interval :
    ∀ (sign : Bool) (q : ℕ) (e_base : ℤ),
      2 ^ (FloatFormat.prec.toNat + 2) ≤ q →
      ∀ (abs_exact : R),
        inStickyInterval (R := R) q e_base abs_exact →
        RMode.round (R := R)
          (if sign then -stickyAbs (R := R) q e_base else stickyAbs (R := R) q e_base) =
        RMode.round (R := R) (if sign then -abs_exact else abs_exact)

/-- Class-driven sticky-bit correctness for `roundIntSigM`. -/
theorem sticky_roundIntSig_eq_round_tc
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeSticky R]
    (sign : Bool) (q : ℕ) (e_base : ℤ)
    (hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q)
    (abs_exact : R)
    (h_exact_in : inStickyInterval (R := R) q e_base abs_exact) :
    roundIntSigM sign (2 * q + 1) e_base =
      RMode.round (R := R) (if sign then -abs_exact else abs_exact) := by
  cases sign with
  | false =>
    have hmag_ne : stickyMag q ≠ 0 := by
      unfold stickyMag
      omega
    rw [show (2 * q + 1) = stickyMag q by rfl,
      roundIntSigM_correct_tc (R := R) false (stickyMag q) e_base hmag_ne]
    change RMode.round (R := R) (intSigVal (R := R) false (stickyMag q) e_base) =
      RMode.round (R := R) abs_exact
    have hsv : intSigVal (R := R) false (stickyMag q) e_base =
        stickyAbs (R := R) q e_base := by
      unfold intSigVal stickyAbs stickyMag
      simp
    rw [hsv]
    exact RModeSticky.round_eq_on_sticky_interval
      (R := R) false q e_base hq_lower abs_exact h_exact_in
  | true =>
    have hmag_ne : stickyMag q ≠ 0 := by
      unfold stickyMag
      omega
    rw [show (2 * q + 1) = stickyMag q by rfl,
      roundIntSigM_correct_tc (R := R) true (stickyMag q) e_base hmag_ne]
    change RMode.round (R := R) (intSigVal (R := R) true (stickyMag q) e_base) =
      RMode.round (R := R) (-abs_exact)
    have hsv : intSigVal (R := R) true (stickyMag q) e_base =
        -stickyAbs (R := R) q e_base := by
      unfold intSigVal stickyAbs stickyMag
      simp
      ring
    rw [hsv]
    exact RModeSticky.round_eq_on_sticky_interval
      (R := R) true q e_base hq_lower abs_exact h_exact_in

/-- The sticky-interval law implies constancy on large odd intervals. -/
theorem round_eq_on_odd_interval_tc
    [RMode R] [RModeSticky R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    RMode.round (R := R) v₁ = RMode.round (R := R) v₂ := by
  let q : ℕ := n / 2
  have hn_eq : n = 2 * q + 1 := by
    have hdiv : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
    dsimp [q]
    omega
  have hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q := by
    have hpow :
        2 * 2 ^ (FloatFormat.prec.toNat + 2) = 2 ^ (FloatFormat.prec.toNat + 3) := by
      have hpow' :
          2 ^ (FloatFormat.prec.toNat + 3) =
            2 ^ (FloatFormat.prec.toNat + 2) * 2 := by
        rw [show FloatFormat.prec.toNat + 3 = (FloatFormat.prec.toNat + 2) + 1 by omega,
          Nat.pow_succ]
      simpa [Nat.mul_comm] using hpow'.symm
    have hlarge2 : 2 * 2 ^ (FloatFormat.prec.toNat + 2) < 2 * q + 1 := by
      calc
        2 * 2 ^ (FloatFormat.prec.toNat + 2) = 2 ^ (FloatFormat.prec.toNat + 3) := hpow
        _ < n := hn_large
        _ = 2 * q + 1 := hn_eq
    by_contra hq_lower
    push_neg at hq_lower
    have hupper : 2 * q + 1 ≤ 2 * 2 ^ (FloatFormat.prec.toNat + 2) := by omega
    exact (not_lt_of_ge hupper) hlarge2
  have hlo :
      (((2 * q + 1 : ℤ) - 1 : R) * (2 : R) ^ e_base) =
        (2 * (q : R)) * (2 : R) ^ e_base := by
    push_cast
    ring
  have hhi :
      (((2 * q + 1 : ℤ) + 1 : R) * (2 : R) ^ e_base) =
        (2 * ((q : R) + 1)) * (2 : R) ^ e_base := by
    push_cast
    ring
  have hv₁_sticky : inStickyInterval (R := R) q e_base v₁ := by
    rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
    unfold inOddInterval oddIntervalLo oddIntervalHi inStickyInterval at *
    rw [hn_eq] at hv₁_lo hv₁_hi
    constructor
    · simpa [hlo] using hv₁_lo
    · calc
        v₁ < (2 * (q : R) + 1 + 1) * (2 : R) ^ e_base := by simpa using hv₁_hi
        _ = (2 * ((q : R) + 1)) * (2 : R) ^ e_base := by ring
  have hv₂_sticky : inStickyInterval (R := R) q e_base v₂ := by
    rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
    unfold inOddInterval oddIntervalLo oddIntervalHi inStickyInterval at *
    rw [hn_eq] at hv₂_lo hv₂_hi
    constructor
    · simpa [hlo] using hv₂_lo
    · calc
        v₂ < (2 * (q : R) + 1 + 1) * (2 : R) ^ e_base := by simpa using hv₂_hi
        _ = (2 * ((q : R) + 1)) * (2 : R) ^ e_base := by ring
  have hround₁ :
      RMode.round (R := R) (stickyAbs (R := R) q e_base) = RMode.round (R := R) v₁ := by
    simpa using (RModeSticky.round_eq_on_sticky_interval
      (R := R) false q e_base hq_lower v₁ hv₁_sticky)
  have hround₂ :
      RMode.round (R := R) (stickyAbs (R := R) q e_base) = RMode.round (R := R) v₂ := by
    simpa using (RModeSticky.round_eq_on_sticky_interval
      (R := R) false q e_base hq_lower v₂ hv₂_sticky)
  calc
    RMode.round (R := R) v₁ = RMode.round (R := R) (stickyAbs (R := R) q e_base) := hround₁.symm
    _ = RMode.round (R := R) v₂ := hround₂

end sticky_roundIntSig

end RoundIntSig
