import Flean.Defs
import Flean.CommonConstants
import Flean.Rounding.Rounding
import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp
import Flean.Rounding.RoundNearest
import Flean.Rounding.OddInterval

/-! # RoundIntSig: Integer Significand Rounding Primitive

This module implements the core rounding primitive `roundIntSig` which takes an exact value
represented as `±mag × 2^e_base` (with `mag : ℕ` and `e_base : ℤ`) and produces an `Fp` result.

This is the shared primitive for softfloat-style arithmetic operations (add, multiply, FMA, etc.).

The algorithm:
1. Compute the bit-length of `mag`
2. Determine the ULP exponent (clamped for subnormals)
3. Shift and round the significand
4. Handle significand overflow (carry into next binade)
5. Handle exponent overflow (produce infinity or largest finite)
-/

section RoundIntSig

variable [FloatFormat]

/-- Determine whether to round up the magnitude, given:
- `mode`: the IEEE 754 rounding mode
- `sign`: true if the result is negative
- `q`: the truncated quotient (integer part after shifting)
- `r`: the remainder (fractional part after shifting)
- `shift`: the number of bits shifted out (so `2^shift` is the divisor) -/
def shouldRoundUp (mode : RoundingMode) (sign : Bool) (q r : ℕ) (shift : ℕ) : Bool :=
  if r = 0 then false
  else match mode with
  | .Down => sign
  | .Up => !sign
  | .TowardZero => false
  | .NearestTiesToEven =>
    let half := 2^(shift - 1)
    if r > half then true
    else if r < half then false
    else q % 2 ≠ 0
  | .NearestTiesAwayFromZero =>
    let half := 2^(shift - 1)
    r ≥ half

omit [FloatFormat] in
/-- Flipping the sign in shouldRoundUp is equivalent to using the conjugate mode with sign=false.
    This is key for reducing sign=true cases to sign=false via negation symmetry. -/
theorem shouldRoundUp_sign_conjugate (mode : RoundingMode) (q r shift : ℕ) :
    shouldRoundUp mode true q r shift = shouldRoundUp mode.conjugate false q r shift := by
  cases mode <;> simp [shouldRoundUp, RoundingMode.conjugate]

/-- IEEE 754 overflow result for a given rounding mode and sign.
- Round-to-nearest modes: always produce infinity
- Down: negative overflows to -∞, positive overflows to largest finite
- Up: positive overflows to +∞, negative overflows to -largest finite
- TowardZero: always produces ±largest finite -/
def handleOverflow (mode : RoundingMode) (sign : Bool) : Fp :=
  match mode with
  | .Down =>
    if sign then Fp.infinite true
    else Fp.finite FiniteFp.largestFiniteFloat
  | .Up =>
    if sign then Fp.finite (-FiniteFp.largestFiniteFloat)
    else Fp.infinite false
  | .TowardZero =>
    if sign then Fp.finite (-FiniteFp.largestFiniteFloat)
    else Fp.finite FiniteFp.largestFiniteFloat
  | .NearestTiesToEven => Fp.infinite sign
  | .NearestTiesAwayFromZero => Fp.infinite sign

-- Helper: if a < 2^b then a * 2^c < 2^(b + c)
omit [FloatFormat] in
private theorem nat_mul_pow2_lt {a b c : ℕ} (h : a < 2^b) : a * 2^c < 2^(b + c) := by
  rw [Nat.pow_add]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos c)).mpr h

-- Helper: if 2^b ≤ a then 2^(b + c) ≤ a * 2^c
omit [FloatFormat] in
private theorem nat_le_mul_pow2 {a b c : ℕ} (h : 2^b ≤ a) : 2^(b + c) ≤ a * 2^c := by
  rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h

-- Helper: for the exact branch, bits_nat + (-shift).toNat ≤ prec.toNat when shift ≤ 0
-- and e_ulp = max(e_base + bits - prec, min_exp - prec + 1)
private theorem exact_branch_m_bound {mag bits_nat neg_shift_nat : ℕ}
    (hmag : mag < 2^bits_nat) (hsum : bits_nat + neg_shift_nat ≤ FloatFormat.prec.toNat) :
    mag * 2^neg_shift_nat < 2^FloatFormat.prec.toNat := by
  calc mag * 2^neg_shift_nat < 2^(bits_nat + neg_shift_nat) := nat_mul_pow2_lt hmag
    _ ≤ 2^FloatFormat.prec.toNat := Nat.pow_le_pow_right (by norm_num) hsum

/-- Round an integer significand to the target floating-point format.

Given an exact value `±mag × 2^e_base` (where `mag : ℕ`, `e_base : ℤ`),
produce the correctly rounded `Fp` result.

This is the core shared primitive for softfloat-style operations. -/
def roundIntSig (mode : RoundingMode) (sign : Bool) (mag : ℕ) (e_base : ℤ) : Fp :=
  if hmag : mag = 0 then
    -- Zero result: preserve sign for signed zero
    Fp.finite (if sign then -0 else 0)
  else
    -- Step 1: bit-length of mag
    let bits : ℤ := (Nat.log2 mag + 1 : ℕ)
    -- Step 2: ULP exponent, clamped for subnormals
    -- In the normal case, we want the ULP step to be 2^(e_base + bits - prec)
    -- For subnormals, the minimum ULP step is 2^(min_exp - prec + 1)
    let e_ulp_normal := e_base + bits - FloatFormat.prec
    let e_ulp_subnormal := FloatFormat.min_exp - FloatFormat.prec + 1
    let e_ulp := max e_ulp_normal e_ulp_subnormal
    -- Step 3: shift = number of bits to discard
    let shift := e_ulp - e_base
    if h_exact : shift ≤ 0 then
      -- No rounding needed: the value is exactly representable (or needs left-shift)
      let m := mag * 2^(-shift).toNat
      let e_stored := e_ulp + FloatFormat.prec - 1
      if h_overflow : e_stored > FloatFormat.max_exp then
        handleOverflow mode sign
      else
        Fp.finite ⟨sign, e_stored, m, by
          -- Need: IsValidFiniteVal e_stored m
          -- Abbreviations for ℕ versions
          set bits_nat := Nat.log2 mag + 1
          have hmag_lt : mag < 2^bits_nat := Nat.lt_log2_self
          have hmag_le : 2^(bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
          -- e_ulp ≥ both branches of the max
          have he_ulp_ge_normal : e_ulp ≥ e_base + bits - FloatFormat.prec := le_max_left _ _
          have he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1 := le_max_right _ _
          -- bits_nat + (-shift).toNat ≤ prec.toNat
          have hsum : bits_nat + (-shift).toNat ≤ FloatFormat.prec.toNat := by
            have hp := FloatFormat.prec_pos; omega
          -- Conjunct 3: m < 2^prec.toNat
          have hm_bound : m < 2^FloatFormat.prec.toNat :=
            exact_branch_m_bound hmag_lt hsum
          -- Conjunct 1: e_stored ≥ min_exp
          have he_ge_min : e_stored ≥ FloatFormat.min_exp := by
            have hp := FloatFormat.valid_prec; omega
          -- Conjunct 2: e_stored ≤ max_exp
          have he_le_max : e_stored ≤ FloatFormat.max_exp := by omega
          -- Conjunct 4: isNormal m ∨ isSubnormal e_stored m
          have h4 : isNormal m ∨ isSubnormal e_stored m := by
            by_cases hm_normal : 2^(FloatFormat.prec - 1).toNat ≤ m
            · -- Normal case: 2^(prec-1) ≤ m
              left; exact ⟨hm_normal, hm_bound⟩
            · -- Subnormal case: m < 2^(prec-1)
              right
              push_neg at hm_normal
              constructor
              · -- e_stored = min_exp
                -- If the normal term dominated the max, then m ≥ 2^(prec-1), contradiction.
                by_contra h_ne
                have he_gt : e_stored > FloatFormat.min_exp := by omega
                -- So e_ulp > min_exp - prec + 1, meaning the normal branch won the max
                have he_ulp_eq : e_ulp = e_base + bits - FloatFormat.prec := by omega
                have hshift_eq : shift = bits - FloatFormat.prec := by omega
                have hneg_shift : (-shift).toNat = (FloatFormat.prec - bits).toNat := by omega
                have hexp_sum : bits_nat - 1 + (-shift).toNat = (FloatFormat.prec - 1).toNat := by
                  have hp := FloatFormat.prec_pos; omega
                have : m ≥ 2^(FloatFormat.prec - 1).toNat := by
                  calc 2^(FloatFormat.prec - 1).toNat
                      = 2^(bits_nat - 1 + (-shift).toNat) := by rw [hexp_sum]
                    _ ≤ mag * 2^(-shift).toNat := nat_le_mul_pow2 hmag_le
                omega
              · -- m ≤ 2^(prec-1).toNat - 1
                omega
          exact ⟨he_ge_min, he_le_max, hm_bound, h4⟩⟩
    else
      -- Step 4: Euclidean division to extract quotient and remainder
      let shift_nat := shift.toNat
      let divisor := 2^shift_nat
      let q := mag / divisor
      let r := mag % divisor
      -- Step 5: Rounding decision
      let roundUp := shouldRoundUp mode sign q r shift_nat
      let m_rounded := if roundUp then q + 1 else q
      -- Step 6: Handle significand overflow (carry into next binade)
      let carry := m_rounded ≥ 2^FloatFormat.prec.toNat
      let m_final := if carry then m_rounded / 2 else m_rounded
      let e_ulp_final := if carry then e_ulp + 1 else e_ulp
      -- Step 7: Compute stored exponent and check for overflow
      let e_stored := e_ulp_final + FloatFormat.prec - 1
      if h_overflow2 : e_stored > FloatFormat.max_exp then
        handleOverflow mode sign
      else
        Fp.finite ⟨sign, e_stored, m_final, by
          -- Need: IsValidFiniteVal e_stored m_final
          -- First, get useful facts
          set bits_nat := Nat.log2 mag + 1
          have hmag_lt : mag < 2^bits_nat := Nat.lt_log2_self
          have hmag_le : 2^(bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
          have he_ulp_ge_normal : e_ulp ≥ e_base + bits - FloatFormat.prec := le_max_left _ _
          have he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1 := le_max_right _ _
          have hshift_pos : shift > 0 := by omega
          -- Key bound: q < 2^prec.toNat
          have hq_bound : q < 2^FloatFormat.prec.toNat := by
            have hsum : FloatFormat.prec.toNat + shift_nat ≥ bits_nat := by
              have hp := FloatFormat.prec_pos; omega
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift_nat)]
            calc mag < 2^bits_nat := hmag_lt
              _ ≤ 2^(FloatFormat.prec.toNat + shift_nat) :=
                Nat.pow_le_pow_right (by norm_num) hsum
              _ = 2^FloatFormat.prec.toNat * 2^shift_nat := by rw [Nat.pow_add]
          -- m_rounded bounds
          have hm_rounded_le : m_rounded ≤ q + 1 := by
            simp only [m_rounded]; split_ifs <;> omega
          have hm_rounded_ge_q : m_rounded ≥ q := by
            simp only [m_rounded]; split_ifs <;> omega
          -- Case-split on the carry condition. First expand let-bindings so split_ifs can see the if.
          show IsValidFiniteVal
            ((if carry then e_ulp + 1 else e_ulp) + FloatFormat.prec - 1)
            (if carry then m_rounded / 2 else m_rounded)
          split_ifs with hcarry
          · -- Carry case: m_final = m_rounded / 2, e_ulp_final = e_ulp + 1
            -- m_rounded = 2^prec.toNat (since q < 2^prec and m_rounded ≤ q+1)
            have hm_rounded_eq : m_rounded = 2^FloatFormat.prec.toNat := by omega
            -- 2^prec / 2 = 2^(prec-1)
            have hp := FloatFormat.prec_toNat_pos
            have hm_div : m_rounded / 2 = 2^(FloatFormat.prec.toNat - 1) := by
              rw [hm_rounded_eq]
              have : (2 : ℕ)^FloatFormat.prec.toNat = 2 * 2^(FloatFormat.prec.toNat - 1) := by
                conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
              omega
            have hprec_eq : FloatFormat.prec.toNat - 1 = (FloatFormat.prec - 1).toNat :=
              FloatFormat.prec_sub_one_toNat_eq_toNat_sub.symm
            have hm_normal : isNormal (m_rounded / 2) := by
              rw [hm_div, hprec_eq]; exact isNormal.sig_msb
            have hm_lt : m_rounded / 2 < 2^FloatFormat.prec.toNat := by
              rw [hm_div, hprec_eq]; exact FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
            have he_ge : e_ulp + 1 + FloatFormat.prec - 1 ≥ FloatFormat.min_exp := by
              have := FloatFormat.valid_prec; omega
            have he_le : e_ulp + 1 + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by omega
            exact ⟨he_ge, he_le, hm_lt, Or.inl hm_normal⟩
          · -- No-carry case: m_final = m_rounded, e_ulp_final = e_ulp
            have hm_lt : m_rounded < 2^FloatFormat.prec.toNat := by omega
            have he_ge : e_ulp + FloatFormat.prec - 1 ≥ FloatFormat.min_exp := by
              have := FloatFormat.valid_prec; omega
            have he_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by omega
            have h4 : isNormal m_rounded ∨ isSubnormal (e_ulp + FloatFormat.prec - 1) m_rounded := by
              by_cases hm_normal : 2^(FloatFormat.prec - 1).toNat ≤ m_rounded
              · left; exact ⟨hm_normal, hm_lt⟩
              · right
                push_neg at hm_normal
                constructor
                · -- If normal branch dominated, q ≥ 2^(prec-1), contradiction
                  by_contra h_ne
                  have he_ulp_gt : e_ulp > FloatFormat.min_exp - FloatFormat.prec + 1 := by omega
                  have he_ulp_eq : e_ulp = e_base + bits - FloatFormat.prec := by omega
                  have hbits_nat_gt : bits_nat > FloatFormat.prec.toNat := by
                    have := FloatFormat.prec_pos; omega
                  have hshift_nat_eq : shift_nat = bits_nat - FloatFormat.prec.toNat := by
                    have := FloatFormat.prec_pos; omega
                  have hq_ge : q ≥ 2^(FloatFormat.prec - 1).toNat := by
                    have hexp_sum : (FloatFormat.prec - 1).toNat + (bits_nat - FloatFormat.prec.toNat) = bits_nat - 1 := by
                      have := FloatFormat.prec_pos; omega
                    have hmul_le : 2 ^ (FloatFormat.prec - 1).toNat * 2 ^ shift_nat ≤ mag := by
                      calc 2 ^ (FloatFormat.prec - 1).toNat * 2 ^ shift_nat
                          = 2 ^ (FloatFormat.prec - 1).toNat * 2 ^ (bits_nat - FloatFormat.prec.toNat) := by rw [hshift_nat_eq]
                        _ = 2 ^ ((FloatFormat.prec - 1).toNat + (bits_nat - FloatFormat.prec.toNat)) := by rw [Nat.pow_add]
                        _ = 2 ^ (bits_nat - 1) := by rw [hexp_sum]
                        _ ≤ mag := hmag_le
                    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift_nat)).mpr hmul_le
                  omega
                · omega
            exact ⟨he_ge, he_le, hm_lt, h4⟩⟩


/-! ## roundIntSig Correctness -/

section roundIntSig_correctness

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- The real value represented by a signed integer `±mag * 2^e_base`. -/
def intSigVal (sign : Bool) (mag : ℕ) (e_base : ℤ) : R :=
  (if sign then -(mag : R) else (mag : R)) * (2 : R) ^ e_base

omit [FloatFormat] [FloorRing R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Reconstruct the signed integer from sign and natAbs: if `sign = decide (n < 0)` and
    `mag = n.natAbs` for nonzero `n`, then `intSigVal sign mag e_base = n * 2^e_base`. -/
theorem intSigVal_eq_int_mul {n : ℤ} (hn : n ≠ 0) (e_base : ℤ) :
    intSigVal (R := R) (decide (n < 0)) n.natAbs e_base = (n : R) * (2 : R) ^ e_base := by
  unfold intSigVal
  by_cases hneg : n < 0
  · simp only [hneg, decide_true, ↓reduceIte]
    -- Goal: -(↑n.natAbs : R) * 2^e_base = (↑n : R) * 2^e_base
    -- Key: (↑n.natAbs : R) = (↑(↑n.natAbs : ℤ) : R) = (↑(-n) : R) = -(↑n : R)
    -- (n.natAbs : R) = (-n : R) since n < 0
    -- Use: ↑n.natAbs = (↑|n| : R) = (|n| : ℤ) → R, and |n| = -n for n < 0
    rw [show (n.natAbs : R) = ((n.natAbs : ℤ) : R) from (Int.cast_natCast n.natAbs).symm,
        Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)]
    push_cast; ring
  · push_neg at hneg
    have hpos : 0 < n := lt_of_le_of_ne hneg (Ne.symm hn)
    simp only [show ¬(n < 0) from not_lt.mpr (le_of_lt hpos), decide_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [show (n.natAbs : R) = ((n.natAbs : ℤ) : R) from (Int.cast_natCast n.natAbs).symm,
        Int.natAbs_of_nonneg (le_of_lt hpos)]

/-- In the overflow case, `handleOverflow` matches `mode.round` for the exact value `intSigVal`. -/
private theorem handleOverflow_eq_round_intSigVal
    (mode : RoundingMode) (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (hmag : mag ≠ 0)
    (hmag_ge : (mag : R) * (2 : R) ^ e_base ≥ (2 : R) ^ (FloatFormat.max_exp + 1)) :
    handleOverflow mode sign = mode.round (intSigVal (R := R) sign mag e_base) := by
  have hmag_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base :=
    mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmag)) (zpow_pos (by norm_num : (0:R) < 2) _)
  have hmag_gt_largest : (mag : R) * (2 : R) ^ e_base > (FiniteFp.largestFiniteFloat.toVal : R) :=
    lt_of_lt_of_le FiniteFp.largestFiniteFloat_lt_maxExp_succ hmag_ge
  have hthresh_le : FloatFormat.overflowThreshold R ≤
      (2 : R) ^ (FloatFormat.max_exp + 1) := by
    rw [show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring,
        ← two_zpow_mul, zpow_one]
    unfold FloatFormat.overflowThreshold
    nlinarith [zpow_pos (by norm_num : (0:R) < 2) FloatFormat.max_exp,
              show (0:R) < 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2 from by positivity]
  have hmag_ge_thresh : (mag : R) * (2 : R) ^ e_base ≥
      FloatFormat.overflowThreshold R :=
    le_trans hthresh_le hmag_ge
  cases sign
  · -- sign = false (positive)
    cases mode <;>
      simp only [handleOverflow, Bool.false_eq_true, ↓reduceIte,
        intSigVal, RoundingMode.round, RoundingMode.toRoundingFunction]
    · exact (roundDown_gt_largestFiniteFloat _ hmag_pos hmag_ge).symm
    · exact (roundUp_gt_largestFiniteFloat _ hmag_pos hmag_gt_largest).symm
    · rw [roundTowardZero_pos_eq _ hmag_pos]
      exact (roundDown_gt_largestFiniteFloat _ hmag_pos hmag_ge).symm
    · exact (rnEven_ge_inf _ hmag_ge_thresh).symm
    · exact (rnAway_ge_inf _ hmag_ge_thresh).symm
  · -- sign = true (negative)
    have hneg_val : -(↑mag : R) * (2:R) ^ e_base < 0 := by linarith
    cases mode <;>
      simp only [handleOverflow, Bool.true_eq_false, ↓reduceIte,
        intSigVal, RoundingMode.round, RoundingMode.toRoundingFunction]
    · -- Down
      rw [neg_mul, roundDown_neg_eq_neg_roundUp _ (ne_of_gt hmag_pos),
          roundUp_gt_largestFiniteFloat _ hmag_pos hmag_gt_largest]
      simp [Fp.neg_def]
    · -- Up
      rw [neg_mul, roundUp_neg_eq_neg_roundDown _ (ne_of_gt hmag_pos),
          roundDown_gt_largestFiniteFloat _ hmag_pos hmag_ge]
      simp [Fp.neg_def]
    · -- TowardZero
      rw [roundTowardZero_neg_eq _ hneg_val,
          neg_mul, roundUp_neg_eq_neg_roundDown _ (ne_of_gt hmag_pos),
          roundDown_gt_largestFiniteFloat _ hmag_pos hmag_ge]
      simp [Fp.neg_def]
    · -- NearestTiesToEven
      rw [neg_mul]; exact (rnEven_neg_overflow _ hmag_pos hmag_ge_thresh).symm
    · -- NearestTiesAwayFromZero
      rw [neg_mul]; exact (rnAway_neg_overflow _ hmag_pos hmag_ge_thresh).symm

/-- All rounding modes are idempotent on non-negative-zero floats. -/
theorem round_idempotent (mode : RoundingMode) (f : FiniteFp)
    (h : f.s = false ∨ 0 < f.m) :
    mode.round (f.toVal (R := R)) = Fp.finite f := by
  cases mode with
  | Down => exact roundDown_idempotent f h
  | Up => exact roundUp_idempotent f h
  | TowardZero => exact roundTowardZero_idempotent f h
  | NearestTiesToEven => exact roundNearestTiesToEven_idempotent f h
  | NearestTiesAwayFromZero => exact roundNearestTiesAwayFromZero_idempotent f h

/-- When the predecessor significand is `2^prec - 1` at the maximum exponent,
the midpoint between the predecessor and its (overflowing) successor equals the
nearest-mode overflow threshold `(2 - 2^(1-prec)/2) * 2^max_exp`. -/
private theorem mid_val_eq_overflow_threshold (q : ℕ) (e_ulp : ℤ)
    (hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat)
    (he_ulp : e_ulp = FloatFormat.max_exp - FloatFormat.prec + 1) :
    (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) =
    (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
  have h2ne : (2 : R) ≠ 0 := by norm_num
  -- (q+1) * 2^e_ulp = 2^(max_exp+1)
  have h_zpow1 : (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ e_ulp =
      (2 : R) ^ (FloatFormat.max_exp + 1) := by
    rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
    congr 1; rw [FloatFormat.prec_toNat_eq]; omega
  have h_zpow2 : (2 : R) ^ e_ulp = 2 * (2 : R) ^ (e_ulp - 1) := by
    rw [show e_ulp = e_ulp - 1 + 1 from by omega, zpow_add₀ h2ne, zpow_one]; ring
  have h_zpow3 : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) *
      (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ e_ulp := by
    rw [two_zpow_mul]; congr 1; omega
  have h_zpow4 : 2 * (2 : R) ^ FloatFormat.max_exp =
      (2 : R) ^ (FloatFormat.max_exp + 1) := by
    rw [zpow_add₀ h2ne, zpow_one]; ring
  have h_prod : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
      (2 : R) ^ (FloatFormat.max_exp + 1) := by
    have hq1 : (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat := by
      exact_mod_cast hq_eq
    have : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
        ((q : R) + 1) * (2 : R) ^ e_ulp := by ring
    rw [this, hq1, h_zpow1]
  linarith [h_prod, h_zpow2, h_zpow3, h_zpow4]

/-- The carry float from `roundUp_nat_mul_zpow_carry` has `toVal = (q+1) * 2^e_ulp`.

When `q + 1 = 2^prec`, the carry float `⟨false, e_ulp + prec, 2^(prec-1), _⟩`
has value `2^prec * 2^(e_ulp+1) / 2 = (q+1) * 2^e_ulp`. -/
private theorem carry_float_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (q : ℕ) (e_ulp : ℤ) (hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat)
    (f : FiniteFp) (hf_s : f.s = false)
    (hf_e : f.e = e_ulp + FloatFormat.prec)
    (hf_m : f.m = 2 ^ (FloatFormat.prec - 1).toNat) :
    (f.toVal : R) = ((q : R) + 1) * (2 : R) ^ e_ulp := by
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two, hf_s, hf_e, hf_m]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub,
      show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1 from by omega]
  push_cast
  rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by exact_mod_cast hq_eq,
      ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
      ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
      two_zpow_mul, two_zpow_mul]
  congr 1
  rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
        have := FloatFormat.valid_prec; omega)]
  omega

/-- The no-carry succ float from `roundUp_nat_mul_zpow` has `toVal = (q+1) * 2^e_ulp`.

The float `⟨false, e_ulp + prec - 1, q + 1, _⟩` has value `(q+1) * 2^(e_ulp+prec-1-prec+1) = (q+1) * 2^e_ulp`. -/
private theorem no_carry_succ_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (q : ℕ) (e_ulp : ℤ)
    (f : FiniteFp) (hf_s : f.s = false)
    (hf_e : f.e = e_ulp + FloatFormat.prec - 1) (hf_m : f.m = q + 1) :
    (f.toVal : R) = ((q : R) + 1) * (2 : R) ^ e_ulp := by
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two, hf_s, hf_e, hf_m]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
  congr 1; ring_nf

/-- When `q + 1 = 2^prec` and `e_ulp + prec > max_exp`, the roundDown predecessor
is the largest finite float and roundUp overflows to infinity.

This is the "carry overflow" scenario in nearest-mode rounding for `roundIntSig`:
the value is just past the largest finite float, roundUp overflows, and the
nearest-mode tie-breaking logic determines the result. -/
private theorem carry_overflow_pred_lff_roundUp_inf
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (mag : ℕ) (e_base e_ulp : ℤ) (q r : ℕ)
    (hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (he_overflow : e_ulp + FloatFormat.prec > FloatFormat.max_exp)
    (hval_pos : (mag : R) * (2 : R) ^ e_base > 0)
    (hval_decomp : (mag : R) * (2:R)^e_base = (q : R) * (2:R)^e_ulp + (r : R) * (2:R)^e_base)
    (hr_pos : r > 0)
    (pred_fp : FiniteFp)
    (hpred_s : pred_fp.s = false)
    (hpred_e : pred_fp.e = e_ulp + FloatFormat.prec - 1)
    (hpred_m : pred_fp.m = q) :
    pred_fp = FiniteFp.largestFiniteFloat ∧
    (mag : R) * (2 : R) ^ e_base > (FiniteFp.largestFiniteFloat.toVal : R) ∧
    roundUp ((mag : R) * (2 : R) ^ e_base) = Fp.infinite false := by
  have hpred_toVal : (pred_fp.toVal : R) = (q : R) * (2 : R) ^ e_ulp := by
    unfold FiniteFp.toVal FiniteFp.sign'
    rw [FloatFormat.radix_val_eq_two, hpred_s, hpred_e, hpred_m]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    congr 1; ring_nf
  have hpred_is_lff : pred_fp = FiniteFp.largestFiniteFloat := by
    have he : e_ulp + FloatFormat.prec - 1 = FloatFormat.max_exp := by omega
    have hq : q = 2 ^ FloatFormat.prec.toNat - 1 := by omega
    ext
    · exact hpred_s
    · rw [hpred_e, he]; rfl
    · rw [hpred_m, hq]; rfl
  have hval_gt_lff : (mag : R) * (2 : R) ^ e_base >
      FiniteFp.largestFiniteFloat.toVal := by
    rw [← hpred_is_lff, hpred_toVal, hval_decomp]
    linarith [mul_pos (Nat.cast_pos.mpr hr_pos)
      (zpow_pos (show (0:R) < 2 from by norm_num) e_base)]
  exact ⟨hpred_is_lff, hval_gt_lff,
    roundUp_gt_largestFiniteFloat _ hval_pos hval_gt_lff⟩

set_option maxHeartbeats 800000 in
/-- `roundIntSig` correctly rounds the value `±mag × 2^e_base` according to the given rounding mode.

This is the core correctness theorem: `roundIntSig` is equivalent to `mode.round` applied to the
exact real value it represents. -/
theorem roundIntSig_correct (mode : RoundingMode) (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (hmag : mag ≠ 0) :
    roundIntSig mode sign mag e_base = mode.round (intSigVal (R := R) sign mag e_base) := by
  unfold roundIntSig
  rw [dif_neg hmag]
  extract_lets bits e_ulp_normal e_ulp_subnormal e_ulp shift
  by_cases h_exact : shift ≤ 0
  · -- EXACT CASE
    simp only [dif_pos h_exact]
    split_ifs with h_overflow
    · -- Exact overflow: value too large for the format
      -- Derive: e_base + bits - 1 ≥ max_exp + 1 (i.e., mag is too large for this exponent)
      set bits_nat := Nat.log2 mag + 1 with hbits_nat_def
      have hmag_le : 2 ^ (bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
      -- Subnormal branch can't overflow (would give e_stored = min_exp ≤ max_exp)
      have : e_ulp_subnormal + FloatFormat.prec - 1 = FloatFormat.min_exp := by omega
      have : FloatFormat.min_exp ≤ FloatFormat.max_exp := by
        linarith [FloatFormat.exp_order]
      have he_ulp_eq : e_ulp = e_ulp_normal := by
        simp only [e_ulp]; exact max_eq_left (by omega)
      have hexp_bound : e_base + ↑bits_nat - 1 ≥ FloatFormat.max_exp + 1 := by omega
      -- (mag : R) * 2^e_base ≥ 2^(max_exp + 1)
      have hmag_val_ge : (mag : R) * (2 : R) ^ e_base ≥ (2 : R) ^ (FloatFormat.max_exp + 1) := by
        have hbits_pos : bits_nat ≥ 1 := by omega
        calc (2 : R) ^ (FloatFormat.max_exp + 1)
            ≤ (2 : R) ^ (e_base + ↑bits_nat - 1) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) hexp_bound
          _ = (2 : R) ^ ((bits_nat - 1 : ℕ) : ℤ) * (2 : R) ^ e_base := by
              rw [two_zpow_mul]; congr 1
              have : ((bits_nat - 1 : ℕ) : ℤ) = (bits_nat : ℤ) - 1 := by omega
              omega
          _ ≤ (mag : R) * (2 : R) ^ e_base := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [zpow_natCast, ← Nat.cast_ofNat, ← Nat.cast_pow]
              exact_mod_cast hmag_le
      exact handleOverflow_eq_round_intSigVal mode sign mag e_base hmag hmag_val_ge
    · -- Exact non-overflow: the result is exactly representable
      set f : FiniteFp := ⟨sign, e_ulp + ↑FloatFormat.prec - 1,
        mag * 2 ^ (-shift).toNat, _⟩
      have hm_pos : 0 < f.m := by
        show 0 < mag * 2 ^ (-shift).toNat
        exact Nat.mul_pos (Nat.pos_of_ne_zero hmag) (Nat.two_pow_pos _)
      have htoVal : f.toVal (R := R) = intSigVal sign mag e_base := by
        show (FiniteFp.toVal (R := R) ⟨sign, e_ulp + ↑FloatFormat.prec - 1,
          mag * 2 ^ (-shift).toNat, _⟩) = intSigVal sign mag e_base
        unfold FiniteFp.toVal FiniteFp.sign' intSigVal
        rw [FloatFormat.radix_val_eq_two]
        push_cast
        rw [← zpow_natCast (2 : R) (-shift).toNat,
            Int.toNat_of_nonneg (show 0 ≤ -shift by omega)]
        have he : e_ulp + ↑FloatFormat.prec - 1 - ↑FloatFormat.prec + 1 = e_ulp := by omega
        rw [he]
        have hexp : (2 : R) ^ (-shift) * (2 : R) ^ e_ulp = (2 : R) ^ e_base := by
          rw [two_zpow_mul]; congr 1; omega
        split_ifs with hs
        · have : (↑mag : R) * (2:R) ^ (-shift) * (2:R) ^ e_ulp = ↑mag * (2:R) ^ e_base := by
            rw [mul_assoc, hexp]
          linarith
        · have : (↑mag : R) * (2:R) ^ (-shift) * (2:R) ^ e_ulp = ↑mag * (2:R) ^ e_base := by
            rw [mul_assoc, hexp]
          linarith
      rw [eq_comm, ← htoVal]
      exact round_idempotent mode f (Or.inr hm_pos)
  · -- ROUNDING CASE: shift > 0, so we need to round
    simp only [dif_neg h_exact]
    -- The goal has all rounding-case let-bindings in context.
    -- Goal: (if e_stored > max_exp then handleOverflow else Fp.finite ⟨sign, e_stored, m_final, ...⟩)
    --       = mode.round (intSigVal sign mag e_base)
    push_neg at h_exact  -- h_exact : 0 < shift
    set bits_nat := Nat.log2 mag + 1 with hbits_nat_def
    have hmag_lt : mag < 2 ^ bits_nat := Nat.lt_log2_self
    have hmag_le : 2 ^ (bits_nat - 1) ≤ mag := Nat.log2_self_le hmag
    have hshift_pos : shift > 0 := h_exact
    have he_ulp_ge_normal : e_ulp ≥ e_ulp_normal := le_max_left _ _
    have he_ulp_ge_sub : e_ulp ≥ e_ulp_subnormal := le_max_right _ _
    have hmag_pos_r : (0 : R) < (mag : R) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmag)
    have hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base :=
      mul_pos hmag_pos_r (zpow_pos (by norm_num : (0:R) < 2) _)
    -- Key: shift.toNat = shift (since shift > 0)
    have hshift_nat_eq : (shift.toNat : ℤ) = shift := Int.toNat_of_nonneg (le_of_lt hshift_pos)
    set shift_nat := shift.toNat
    set q := mag / 2 ^ shift_nat
    set r := mag % 2 ^ shift_nat
    have hmag_eq : mag = 2 ^ shift_nat * q + r := (Nat.div_add_mod mag (2 ^ shift_nat)).symm
    have hr_bound : r < 2 ^ shift_nat := Nat.mod_lt mag (Nat.two_pow_pos shift_nat)
    -- q < 2^prec
    have hq_bound : q < 2 ^ FloatFormat.prec.toNat := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift_nat)]
      calc mag < 2 ^ bits_nat := hmag_lt
        _ ≤ 2 ^ (FloatFormat.prec.toNat + shift_nat) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := FloatFormat.prec_pos; omega
        _ = 2 ^ FloatFormat.prec.toNat * 2 ^ shift_nat := by rw [Nat.pow_add]
    -- Value decomposition: mag * 2^e_base = q * 2^e_ulp + r * 2^e_base
    have hshift_zpow : (2 : R) ^ (shift_nat : ℕ) * (2 : R) ^ e_base = (2 : R) ^ e_ulp := by
      rw [← zpow_natCast (2 : R) shift_nat, hshift_nat_eq, two_zpow_mul]
      congr 1; omega
    have hval_decomp : (mag : R) * (2:R)^e_base = (q : R) * (2:R)^e_ulp + (r : R) * (2:R)^e_base := by
      have hmag_cast : (mag : R) = (q : R) * ((2 : R) ^ (shift_nat : ℕ)) + (r : R) := by
        have h := hmag_eq  -- mag = 2^shift_nat * q + r in ℕ
        have : (mag : R) = (2 ^ shift_nat * q + r : ℕ) := by exact_mod_cast h
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at this
        linarith
      calc (mag : R) * (2:R)^e_base
          = ((q : R) * (2 : R) ^ (shift_nat : ℕ) + (r : R)) * (2:R)^e_base := by rw [hmag_cast]
        _ = (q : R) * ((2 : R) ^ (shift_nat : ℕ) * (2:R)^e_base) + (r : R) * (2:R)^e_base := by ring
        _ = (q : R) * (2 : R) ^ e_ulp + (r : R) * (2:R)^e_base := by rw [hshift_zpow]
    -- Int.log correspondence
    have hint_log : Int.log 2 ((mag : R) * (2:R)^e_base) = (Nat.log2 mag : ℤ) + e_base :=
      int_log_nat_mul_zpow mag e_base hmag
    -- The goal already has let-bindings extracted.
    -- Split on the overflow check
    split_ifs with h_overflow2
    · -- Overflow after rounding: handleOverflow = mode.round(intSigVal ...)
      -- Case split on whether the no-carry branch already overflows
      by_cases hnocarry_overflow : e_ulp + FloatFormat.prec - 1 > FloatFormat.max_exp
      · -- No-carry overflow: e_base + bits - 1 > max_exp ⇒ mag * 2^e_base ≥ 2^(max_exp+1)
        have hbits_eq : bits = (bits_nat : ℤ) := by simp [bits_nat, bits]
        have he_normal : e_ulp_normal = e_base + (bits_nat : ℤ) - FloatFormat.prec := by
          rw [show e_ulp_normal = e_base + bits - FloatFormat.prec from rfl, hbits_eq]
        have hbits_nat_pos : bits_nat ≥ 1 := by omega
        -- The subnormal branch can't cause overflow: e_ulp_subnormal + prec - 1 = min_exp ≤ max_exp
        have he_ulp_eq_normal : e_ulp = e_ulp_normal := by
          -- If subnormal dominates: e_ulp = e_ulp_subnormal, e_ulp + prec - 1 = min_exp ≤ max_exp
          -- This contradicts hnocarry_overflow. So normal must dominate.
          have h_sub_bound : e_ulp_subnormal + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by
            show FloatFormat.min_exp - FloatFormat.prec + 1 + FloatFormat.prec - 1 ≤ FloatFormat.max_exp
            linarith [FloatFormat.exp_order]
          -- e_ulp = max(normal, subnormal). If normal < subnormal, then e_ulp = subnormal, contradiction.
          rcases le_or_gt e_ulp_subnormal e_ulp_normal with h | h
          · exact max_eq_left h
          · exfalso; have : e_ulp = e_ulp_subnormal := max_eq_right (le_of_lt h)
            linarith
        have hexp_bound : e_base + ↑bits_nat - 1 ≥ FloatFormat.max_exp + 1 := by
          have : e_ulp = e_base + (bits_nat : ℤ) - FloatFormat.prec := by rw [he_ulp_eq_normal, he_normal]
          have := FloatFormat.prec_pos
          omega
        have hmag_ge : (mag : R) * (2 : R) ^ e_base ≥ (2 : R) ^ (FloatFormat.max_exp + 1) := by
          calc (2 : R) ^ (FloatFormat.max_exp + 1)
              ≤ (2 : R) ^ (e_base + ↑bits_nat - 1) :=
                zpow_le_zpow_right₀ (by norm_num) hexp_bound
            _ = (2 : R) ^ ((bits_nat - 1 : ℕ) : ℤ) * (2 : R) ^ e_base := by
                rw [two_zpow_mul]; congr 1
                have : bits_nat ≥ 1 := by omega
                omega
            _ ≤ (mag : R) * (2 : R) ^ e_base := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                rw [zpow_natCast, ← Nat.cast_ofNat, ← Nat.cast_pow]; exact_mod_cast hmag_le
        exact handleOverflow_eq_round_intSigVal mode sign mag e_base hmag hmag_ge
      · -- Carry overflow: e_ulp + prec - 1 ≤ max_exp but e_stored > max_exp
        push_neg at hnocarry_overflow
        -- h_overflow2 involves opaque let-bindings for e_stored✝.
        -- Key insight: the let-bound vars are definitionally equal to our set-bound vars.
        -- We can use `change` to restate h_overflow2 with visible terms.
        -- e_stored✝ = (if carry✝ then e_ulp + 1 else e_ulp) + prec - 1
        -- carry✝ = m_rounded✝ ≥ 2^prec.toNat
        -- m_rounded✝ = if roundUp✝ then q✝ + 1 else q✝
        -- roundUp✝ = shouldRoundUp mode sign q✝ r✝ shift_nat✝
        -- q✝ = mag / 2^shift_nat✝, r✝ = mag % 2^shift_nat✝, shift_nat✝ = shift.toNat
        -- All of these are definitionally equal to q, r, shift_nat, etc.
        -- Fully expand h_overflow2
        set roundUp_val := shouldRoundUp mode sign q r shift_nat with hroundup_def
        set m_rounded := if roundUp_val then q + 1 else q with hm_rounded_def
        set carry := decide (m_rounded ≥ 2 ^ FloatFormat.prec.toNat) with hcarry_def
        change (if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) +
          FloatFormat.prec - 1 > FloatFormat.max_exp at h_overflow2
        -- Now h_overflow2 has visible if-then-else that split_ifs can handle
        split_ifs at h_overflow2 with h_carry
        swap
        · -- ¬carry case: m_rounded < 2^prec, so e_stored = e_ulp + prec - 1 ≤ max_exp
          -- h_overflow2 : e_ulp + prec - 1 > max_exp, contradicts hnocarry_overflow
          exact absurd h_overflow2 (not_lt.mpr hnocarry_overflow)
        · -- carry = true: m_rounded ≥ 2^prec
          -- h_overflow2 : e_ulp + 1 + prec - 1 > max_exp
          -- Combined with hnocarry_overflow: e_ulp + prec - 1 ≤ max_exp
          -- ⇒ e_ulp + prec - 1 = max_exp, i.e. e_ulp = max_exp - prec + 1
          have he_ulp_eq : e_ulp = FloatFormat.max_exp - FloatFormat.prec + 1 := by omega
          -- From carry: m_rounded ≥ 2^prec, and q < 2^prec
          -- If roundUp_val = false, m_rounded = q < 2^prec, contradiction
          have hroundup : roundUp_val = true := by
            by_contra h; simp only [Bool.not_eq_true] at h
            have : m_rounded = q := by rw [hm_rounded_def]; simp [h]
            linarith [hq_bound]
          -- roundUp_val = true ⇒ m_rounded = q + 1 ≥ 2^prec ⇒ q = 2^prec - 1
          have hm_eq : m_rounded = q + 1 := by rw [hm_rounded_def]; simp [hroundup]
          have hq_ge : q + 1 ≥ 2 ^ FloatFormat.prec.toNat := by
            have h1 := h_carry; rw [hm_eq] at h1; exact h1
          have hq_eq : q = 2 ^ FloatFormat.prec.toNat - 1 :=
            Nat.eq_sub_of_add_eq (Nat.le_antisymm hq_bound hq_ge)
          -- r > 0 (since shouldRoundUp requires r ≠ 0)
          have hr_pos : r > 0 := by
            by_contra h; push_neg at h; have hr0 : r = 0 := by omega
            have : shouldRoundUp mode sign q r shift_nat = false := by
              unfold shouldRoundUp; simp [hr0]
            rw [hroundup_def] at hroundup; simp [this] at hroundup
          -- mag * 2^e_base > lff.toVal
          have hmag_gt_lff : (mag : R) * (2 : R) ^ e_base > (FiniteFp.largestFiniteFloat.toVal : R) := by
            -- mag = 2^shift * q + r > 2^shift * q = 2^shift * (2^prec - 1)
            -- mag * 2^e_base > q * 2^shift * 2^e_base = q * 2^e_ulp
            -- = (2^prec - 1) * 2^(max_exp - prec + 1) = lff.toVal
            have hmag_gt_q : mag > 2 ^ shift_nat * q := by omega
            have hmag_gt_r : (mag : R) > (q : R) * (2 : R) ^ (shift_nat : ℕ) := by
              have : (2 ^ shift_nat * q : ℕ) < mag := hmag_gt_q
              have h := (Nat.cast_lt (α := R)).mpr this
              simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
              linarith
            calc (FiniteFp.largestFiniteFloat.toVal : R)
                = ((2 : R) ^ FloatFormat.prec - 1) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
                  rw [FiniteFp.largestFiniteFloat_toVal, sub_mul]
                  have h1 : (2 : R) ^ FloatFormat.max_exp * 2 = (2 : R) ^ FloatFormat.prec * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
                    rw [mul_comm, show (2 : R) * (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ (FloatFormat.max_exp + 1) from by
                      rw [show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring, ← two_zpow_mul, zpow_one]]
                    rw [two_zpow_mul]; congr 1; ring
                  have h2 : (2 : R) ^ FloatFormat.max_exp * (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) =
                      1 * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) := by
                    rw [one_mul, two_zpow_mul]; congr 1; ring
                  linarith
              _ = (q : R) * (2 : R) ^ e_ulp := by
                  congr 1
                  · -- (2^prec - 1 : R) = (q : R)
                    rw [hq_eq]; push_cast [Nat.one_le_two_pow]
                    rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
                  · -- 2^(max_exp - prec + 1) = 2^e_ulp
                    rw [he_ulp_eq]
              _ = (q : R) * ((2 : R) ^ (shift_nat : ℕ) * (2 : R) ^ e_base) := by rw [hshift_zpow]
              _ < (mag : R) * (2 : R) ^ e_base := by nlinarith [zpow_pos (show (0:R) < 2 by norm_num) e_base]
          -- Helper for nearest modes: derive threshold bound using r ≥ half
          have hmag_ge_thresh_of_half (hr_half : r ≥ 2 ^ (shift_nat - 1)) :
              (mag : R) * (2 : R) ^ e_base ≥
              FloatFormat.overflowThreshold R := by
            -- mid_val = threshold
            have hmid_eq := mid_val_eq_overflow_threshold (R := R) q e_ulp
              (show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega) he_ulp_eq
            -- val ≥ mid_val: r * 2^e_base ≥ 2^(shift_nat-1) * 2^e_base = 2^(e_ulp-1)
            have hr_cast : (r : R) ≥ (2^(shift_nat - 1) : ℕ) := by exact_mod_cast hr_half
            have h_half_zpow : (2:R)^((shift_nat - 1 : ℕ) : ℤ) * (2:R)^e_base = (2:R)^(e_ulp - 1) := by
              rw [two_zpow_mul]; congr 1
              have : shift_nat ≥ 1 := by omega
              omega
            have h_nat_zpow : ((2^(shift_nat - 1) : ℕ) : R) = (2:R)^((shift_nat - 1 : ℕ) : ℤ) := by
              rw [zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
            -- val = q * 2^e_ulp + r * 2^e_base ≥ q * 2^e_ulp + 2^(e_ulp-1) = threshold
            unfold FloatFormat.overflowThreshold at *
            nlinarith [hval_decomp, zpow_pos (show (0:R) < 2 by norm_num) e_base]
          -- Now dispatch per mode
          cases sign
          · -- sign = false (positive)
            cases mode <;>
              simp only [handleOverflow, Bool.false_eq_true, ↓reduceIte,
                intSigVal, RoundingMode.round, RoundingMode.toRoundingFunction]
            · exact (roundDown_gt_lff _ hval_pos hmag_gt_lff).symm
            · exact (roundUp_gt_largestFiniteFloat _ hval_pos hmag_gt_lff).symm
            · rw [roundTowardZero_pos_eq _ hval_pos]
              exact (roundDown_gt_lff _ hval_pos hmag_gt_lff).symm
            · -- NearestTiesToEven: need r ≥ half
              have hr_half : r ≥ 2 ^ (shift_nat - 1) := by
                have hsu := hroundup_def ▸ hroundup
                unfold shouldRoundUp at hsu
                simp only [show r ≠ 0 from by omega, ↓reduceIte] at hsu
                split_ifs at hsu with h1 h2 <;> omega
              exact (rnEven_ge_inf _ (hmag_ge_thresh_of_half hr_half)).symm
            · -- NearestTiesAway: need r ≥ half
              have hr_half : r ≥ 2 ^ (shift_nat - 1) := by
                have hsu := hroundup_def ▸ hroundup
                unfold shouldRoundUp at hsu
                simp only [show r ≠ 0 from by omega, ↓reduceIte] at hsu
                exact decide_eq_true_eq.mp hsu
              exact (rnAway_ge_inf _ (hmag_ge_thresh_of_half hr_half)).symm
          · -- sign = true (negative)
            have hneg_val : -(↑mag : R) * (2:R) ^ e_base < 0 := by linarith
            cases mode <;>
              simp only [handleOverflow, Bool.true_eq_false, ↓reduceIte,
                intSigVal, RoundingMode.round, RoundingMode.toRoundingFunction]
            · rw [neg_mul, roundDown_neg_eq_neg_roundUp _ (ne_of_gt hval_pos),
                  roundUp_gt_largestFiniteFloat _ hval_pos hmag_gt_lff]
              rfl
            · rw [neg_mul, roundUp_neg_eq_neg_roundDown _ (ne_of_gt hval_pos),
                  roundDown_gt_lff _ hval_pos hmag_gt_lff]
              rfl
            · rw [roundTowardZero_neg_eq _ hneg_val,
                  neg_mul, roundUp_neg_eq_neg_roundDown _ (ne_of_gt hval_pos),
                  roundDown_gt_lff _ hval_pos hmag_gt_lff]
              rfl
            · -- NearestTiesToEven: need threshold bound
              have hr_half : r ≥ 2 ^ (shift_nat - 1) := by
                have hsu := hroundup_def ▸ hroundup
                unfold shouldRoundUp at hsu
                simp only [show r ≠ 0 from by omega, ↓reduceIte] at hsu
                split_ifs at hsu with h1 h2 <;> omega
              rw [neg_mul]; exact (rnEven_neg_overflow _ hval_pos (hmag_ge_thresh_of_half hr_half)).symm
            · -- NearestTiesAway: need threshold bound
              have hr_half : r ≥ 2 ^ (shift_nat - 1) := by
                have hsu := hroundup_def ▸ hroundup
                unfold shouldRoundUp at hsu
                simp only [show r ≠ 0 from by omega, ↓reduceIte] at hsu
                exact decide_eq_true_eq.mp hsu
              rw [neg_mul]; exact (rnAway_neg_overflow _ hval_pos (hmag_ge_thresh_of_half hr_half)).symm
    · -- Non-overflow: Fp.finite ⟨sign, e_stored, m_final, ...⟩ = mode.round(intSigVal ...)
      rename_i h_not_overflow
      -- Name the opaque let-bound variables
      set roundUp_val := shouldRoundUp mode sign q r shift_nat with hroundup_def
      set m_rounded := if roundUp_val then q + 1 else q with hm_rounded_def
      push_neg at h_not_overflow
      -- Resolve the opaque let-bindings in the goal
      change Fp.finite ⟨sign,
        (if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) + FloatFormat.prec - 1,
        if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then m_rounded / 2 else m_rounded,
        _⟩ = mode.round (intSigVal sign mag e_base)
      -- shouldRoundUp returns false when r = 0
      have hru_exact : r = 0 → roundUp_val = false := by
        intro hr0; rw [hroundup_def]; unfold shouldRoundUp; simp [hr0]
      -- Exact value bridge: when r = 0, intSigVal = ±q * 2^e_ulp
      have hf_exact_val : r = 0 → (intSigVal (R := R) sign mag e_base) =
          (if sign then -(q : R) else (q : R)) * (2 : R) ^ e_ulp := by
        intro hr0
        have hmag_exact : mag = 2 ^ shift_nat * q := by omega
        unfold intSigVal
        have hmag_cast : (mag : R) = (q : R) * (2 : R) ^ (shift_nat : ℕ) := by
          rw [hmag_exact]; push_cast; ring
        rw [hmag_cast]
        have hexp_eq : (2 : R) ^ (shift_nat : ℕ) * (2 : R) ^ e_base = (2 : R) ^ e_ulp := by
          rw [← zpow_natCast (2:R) shift_nat, hshift_nat_eq, two_zpow_mul]
          congr 1; omega
        split_ifs with hs
        · -- sign = true: -(↑q * 2^shift_nat) * 2^e_base = -(↑q) * 2^e_ulp
          have : (q : R) * (2 : R) ^ (shift_nat : ℕ) * (2 : R) ^ e_base =
              (q : R) * (2 : R) ^ e_ulp := by
            rw [mul_assoc]; exact congrArg _ hexp_eq
          linarith
        · -- sign = false: ↑q * 2^shift_nat * 2^e_base = ↑q * 2^e_ulp
          rw [mul_assoc]; exact congrArg _ hexp_eq
      by_cases hr0 : r = 0
      · -- EXACT CASE: r = 0, value is exactly q * 2^e_ulp
        have hru_false : roundUp_val = false := hru_exact hr0
        have hm_eq : m_rounded = q := by rw [hm_rounded_def]; simp [hru_false]
        have hno_carry : ¬(m_rounded ≥ 2 ^ FloatFormat.prec.toNat) := by omega
        simp only [hno_carry, if_false, ite_false]
        -- When r = 0 and q = 0, mag = 0 which contradicts hmag
        have hq_ne_zero : q ≠ 0 := by
          intro hq0; apply hmag
          have h1 : mag = 2 ^ shift_nat * q + r := hmag_eq
          rw [hr0, hq0] at h1; simp at h1; exact h1
        -- The constructed float = mode.round(intSigVal ...) via idempotence
        set f : FiniteFp := ⟨sign, e_ulp + FloatFormat.prec - 1, q, _⟩
        have htoVal : f.toVal (R := R) = intSigVal sign mag e_base := by
          show (FiniteFp.toVal (R := R) ⟨sign, e_ulp + FloatFormat.prec - 1, q, _⟩) =
            intSigVal sign mag e_base
          unfold FiniteFp.toVal FiniteFp.sign'
          rw [FloatFormat.radix_val_eq_two]
          push_cast
          rw [show e_ulp + ↑FloatFormat.prec - 1 - ↑FloatFormat.prec + 1 = e_ulp from by omega]
          rw [hf_exact_val hr0]
          split_ifs <;> ring
        have hm_pos_or_sign : f.s = false ∨ 0 < f.m := by
          right; exact Nat.pos_of_ne_zero hq_ne_zero
        -- The goal has m_rounded but f has m = q. Unfold m_rounded → q.
        simp only [hm_eq]
        rw [eq_comm, ← htoVal]
        exact round_idempotent mode f hm_pos_or_sign
      · -- INEXACT CASE: r > 0
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        -- The value val = mag * 2^e_base is not exactly representable (r > 0).
        -- roundIntSig computes q = mag / 2^shift_nat (truncation) and optionally rounds up.
        -- The rounding functions (roundDown, roundUp) compute the same floor/ceiling.
        --
        -- KEY BRIDGE: q = ⌊(mag * 2^e_base) / 2^e_ulp⌋ (as naturals)
        -- because (mag * 2^e_base) / 2^e_ulp = mag / 2^shift (since shift = e_ulp - e_base)
        -- and ⌊mag / 2^shift⌋ = mag / 2^shift_nat (Euclidean division).
        --
        -- Then findPredecessorPos(val) produces the float with significand q and exponent e_ulp+prec-1,
        -- and findSuccessorPos(val) produces the float with significand q+1 (or with carry).
        -- Finally, shouldRoundUp is consistent with mode.round choosing the correct neighbor.
        --
        -- Step 1: Show val is not in overflow range
        -- (h_not_overflow says e_stored ≤ max_exp, so val < 2^(max_exp+1) or barely above)
        -- We need val < 2^(max_exp+1) for findPredecessorPos to enter subnormal/normal
        -- e_stored = (if carry then e_ulp+1 else e_ulp) + prec - 1 ≤ max_exp
        -- In the no-carry case: e_ulp + prec - 1 ≤ max_exp, so e_ulp ≤ max_exp - prec + 1
        -- Since mag < 2^bits_nat and shift = e_ulp - e_base, val = mag * 2^e_base < 2^bits_nat * 2^e_base
        -- = 2^(bits_nat + e_base) = 2^(e_ulp_normal + prec) ≤ 2^(e_ulp + prec) ≤ 2^(max_exp + 1)
        have hval_lt_overflow : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1) := by
          -- From h_not_overflow: e_stored ≤ max_exp, and e_stored ≥ e_ulp + prec - 1
          -- (regardless of carry, since carry only adds 1 to e_ulp, but also implies
          --  q+1 ≥ 2^prec, meaning q ≥ 2^prec - 1, but then the carry case has
          --  e_stored = e_ulp + 1 + prec - 1 ≤ max_exp, so e_ulp + prec ≤ max_exp)
          -- Simplest: e_ulp + prec - 1 ≤ e_stored ≤ max_exp
          -- This gives e_ulp ≤ max_exp - prec + 1, so e_ulp + prec ≤ max_exp + 1.
          -- val = mag * 2^e_base < 2^bits_nat * 2^e_base = 2^(e_ulp_normal + prec)
          -- ≤ 2^(e_ulp + prec) ≤ 2^(max_exp + 1)
          have he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by
            -- From the non-overflow hypothesis: e_stored ≤ max_exp
            -- e_stored = (if carry then e_ulp+1 else e_ulp) + prec - 1 ≥ e_ulp + prec - 1
            -- So e_ulp + prec - 1 ≤ max_exp
            have : ¬((if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) +
                  FloatFormat.prec - 1 > FloatFormat.max_exp) := by
              -- This is exactly the negated condition from the split_ifs
              assumption
            push_neg at this
            linarith [show e_ulp ≤ (if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) from
              by split_ifs <;> omega]
          have hbits_eq : bits = (bits_nat : ℤ) := by simp [bits_nat, bits]
          calc (mag : R) * (2 : R) ^ e_base
              < (2 : R) ^ (bits_nat : ℕ) * (2 : R) ^ e_base := by
                apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num) _)
                rw [← Nat.cast_ofNat, ← Nat.cast_pow]; exact_mod_cast hmag_lt
            _ = (2 : R) ^ ((bits_nat : ℤ) + e_base) := by
                rw [show (2 : R) ^ (bits_nat : ℕ) = (2 : R) ^ (bits_nat : ℤ) from
                  (zpow_natCast (2 : R) bits_nat).symm, ← two_zpow_mul]
            _ ≤ (2 : R) ^ (FloatFormat.max_exp + 1) := by
                apply zpow_le_zpow_right₀ (by norm_num)
                have : e_ulp ≥ e_ulp_normal := le_max_left _ _
                have hp := FloatFormat.prec_pos; omega
        -- FLOOR BRIDGE: ⌊val / 2^e_ulp⌋ = q (as ℤ)
        -- val / 2^e_ulp = mag / 2^shift_nat, and ⌊(mag:R) / 2^shift_nat⌋ = q
        have hval_div : (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp =
            (mag : R) / ((2 : R) ^ (shift_nat : ℕ)) := by
          rw [mul_div_assoc,
            show (2 : R) ^ e_base / (2 : R) ^ e_ulp = (2 : R) ^ (e_base - e_ulp) from
              by rw [← zpow_sub₀ (by norm_num : (2:R) ≠ 0)],
            show e_base - e_ulp = -shift from by omega,
            show -shift = -(shift_nat : ℤ) from by rw [hshift_nat_eq],
            zpow_neg, zpow_natCast, div_eq_mul_inv]
        have hfloor_bridge : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ) := by
          rw [hval_div, show (2 : R) ^ (shift_nat : ℕ) = ((2 ^ shift_nat : ℕ) : R) from by
            push_cast; rfl]
          rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
        -- CEIL BRIDGE: ⌈val / 2^e_ulp⌉ = q + 1 (when r > 0)
        have hceil_bridge : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1 := by
          rw [hval_div, Int.ceil_eq_iff]
          -- Need: (q + 1 : ℤ) - 1 < (mag : R) / 2^shift_nat ∧ (mag : R) / 2^shift_nat ≤ (q + 1 : ℤ)
          have hpow_pos : (0 : R) < (2 : R) ^ (shift_nat : ℕ) := by positivity
          -- mag = 2^shift_nat * q + r, so (mag:R) / 2^shift_nat = q + r / 2^shift_nat
          have hval_split : (mag : R) / (2 : R) ^ (shift_nat : ℕ) =
              (q : R) + (r : R) / (2 : R) ^ (shift_nat : ℕ) := by
            rw [hmag_eq]; push_cast; rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hpow_pos)]
          rw [hval_split]
          constructor
          · -- (↑(q+1) : R) - 1 < q + r / 2^shift_nat
            have hr_pos_r : (0 : R) < (r : R) := Nat.cast_pos.mpr hr_pos
            have : (0 : R) < (r : R) / (2 : R) ^ (shift_nat : ℕ) := div_pos hr_pos_r hpow_pos
            push_cast [Int.cast_add, Int.cast_one, Int.cast_natCast]
            linarith
          · -- q + r / 2^shift_nat ≤ (↑(q+1) : R)
            have : (r : R) / (2 : R) ^ (shift_nat : ℕ) ≤ 1 := by
              rw [div_le_one hpow_pos]
              exact_mod_cast le_of_lt hr_bound
            push_cast [Int.cast_add, Int.cast_one, Int.cast_natCast]
            linarith
        -- The proof now proceeds by case-splitting on mode and sign.
        -- For each combination, we determine shouldRoundUp's value,
        -- then show the result equals the appropriate rounding function applied to intSigVal.
        -- We use hfloor_bridge and hceil_bridge to connect roundIntSig's Nat division
        -- to the floor/ceil used by roundDown/roundUp.
        -- Step 1: Establish key hypotheses for roundDown_nat_mul_zpow
        have he_stored_le_inner : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp := by
          have : ¬((if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) +
                FloatFormat.prec - 1 > FloatFormat.max_exp) := by assumption
          push_neg at this
          linarith [show e_ulp ≤ (if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) from
            by split_ifs <;> omega]
        have h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
            (FloatFormat.min_exp - FloatFormat.prec + 1) := by
          show e_ulp = max e_ulp_normal e_ulp_subnormal
          rfl
        -- Step 2: roundDown(val) = Fp.finite ⟨false, e_ulp+prec-1, q, _⟩
        have hroundDown_eq : roundDown ((mag : R) * (2 : R) ^ e_base) =
            Fp.finite ⟨false, e_ulp + FloatFormat.prec - 1, q, _⟩ :=
          roundDown_nat_mul_zpow mag e_base e_ulp q hmag hval_pos hval_lt_overflow
            hfloor_bridge hint_log (by omega) he_stored_le_inner hq_bound trivial h_e_ulp_eq
        -- pred_fp and its toVal
        set pred_fp : FiniteFp := ⟨false, e_ulp + FloatFormat.prec - 1, q, _⟩ with hpred_fp_def
        have hpred_toVal : pred_fp.toVal (R := R) = (q : R) * (2 : R) ^ e_ulp := by
          simp only [FiniteFp.toVal, pred_fp, FiniteFp.sign', FloatFormat.radix_val_eq_two,
            Bool.false_eq_true, ↓reduceIte, one_mul]
          congr 1; ring_nf
        -- half = 2^(shift_nat - 1) as Nat
        set half := 2^(shift_nat - 1) with hhalf_def
        have hshift_ge_one : shift_nat ≥ 1 := by omega
        -- Bridge: (half : R) * 2^e_base = 2^(e_ulp - 1)
        have hhalf_zpow : (half : R) * (2 : R) ^ e_base = (2 : R) ^ (e_ulp - 1) := by
          rw [hhalf_def, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast (2 : R) (shift_nat - 1),
              two_zpow_mul]
          congr 1
          have : ((shift_nat - 1 : ℕ) : ℤ) = (shift_nat : ℤ) - 1 := by omega
          omega
        -- Define the midpoint value
        set mid_val : R := (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) with hmid_val_def
        -- val - mid = (r - half) * 2^e_base
        have hval_sub_mid : (mag : R) * (2 : R) ^ e_base - mid_val =
            ((r : R) - (half : R)) * (2 : R) ^ e_base := by
          rw [hmid_val_def, hval_decomp, ← hhalf_zpow]; ring
        -- val vs midpoint: one-directional helpers
        have h2pos_e : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num) _
        have hr_lt_mid : r < half → (mag : R) * (2:R)^e_base < mid_val := by
          intro h
          have : ((r : R) - (half : R)) * (2 : R) ^ e_base < 0 :=
            mul_neg_of_neg_of_pos (by exact_mod_cast sub_neg.mpr (show (r : ℤ) < half by omega)) h2pos_e
          linarith [hval_sub_mid]
        have hr_gt_mid : r > half → (mag : R) * (2:R)^e_base > mid_val := by
          intro h
          have : ((r : R) - (half : R)) * (2 : R) ^ e_base > 0 :=
            mul_pos (by exact_mod_cast sub_pos.mpr (show (half : ℤ) < r by omega)) h2pos_e
          linarith [hval_sub_mid]
        have hr_eq_mid : r = half → (mag : R) * (2:R)^e_base = mid_val := by
          intro h
          have : ((r : R) - (half : R)) * (2 : R) ^ e_base = 0 := by
            have : (r : R) = (half : R) := by exact_mod_cast h
            rw [this, sub_self, zero_mul]
          linarith [hval_sub_mid]
        -- isEvenSignificand pred_fp = decide (q % 2 = 0)
        have hpred_even : isEvenSignificand pred_fp = decide (q % 2 = 0) := by
          simp [isEvenSignificand, pred_fp]
        -- Midpoint bridge: (pred_fp.toVal + f.toVal) / 2 = mid_val
        -- for any successor f whose toVal = (q+1) * 2^e_ulp
        have hmid_unfold : ∀ (f : FiniteFp), (f.toVal : R) = ((q : R) + 1) * (2 : R) ^ e_ulp →
            (pred_fp.toVal (R := R) + f.toVal) / 2 = mid_val := by
          intro f hf
          rw [hpred_toVal, hf, hmid_val_def,
            show (2 : R) ^ (e_ulp - 1) = (2 : R) ^ e_ulp / 2 from by
              rw [zpow_sub₀ (by norm_num : (2:R) ≠ 0), zpow_one]]
          ring
        -- Step 3: Case split on shouldRoundUp
        by_cases hru : roundUp_val = true
        · -- shouldRoundUp = true → m_rounded = q + 1
          have hm_eq : m_rounded = q + 1 := by rw [hm_rounded_def]; simp [hru]
          -- Sub-case split on carry
          by_cases hcarry : m_rounded ≥ 2 ^ FloatFormat.prec.toNat
          · -- CARRY CASE: q + 1 ≥ 2^prec → q = 2^prec - 1
            have hq_eq : q = 2 ^ FloatFormat.prec.toNat - 1 :=
              Nat.eq_sub_of_add_eq (Nat.le_antisymm hq_bound (by omega))
            -- m_rounded / 2 = 2^(prec-1), e_stored = e_ulp + 1 + prec - 1 = e_ulp + prec
            simp only [hcarry, if_true, ite_true]
            -- m_rounded = 2^prec, so m_rounded / 2 = 2^(prec-1)
            have hm_eq2 : m_rounded = 2 ^ FloatFormat.prec.toNat := by omega
            have hm_div : m_rounded / 2 = 2 ^ (FloatFormat.prec.toNat - 1) := by
              rw [hm_eq2]
              have hp : 1 ≤ FloatFormat.prec.toNat := by
                have := FloatFormat.valid_prec; omega
              rw [Nat.pow_div hp (by norm_num)]
            -- e_ulp + prec ≤ max_exp from non-overflow
            have he_stored_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp := by
              have : ¬((if m_rounded ≥ 2 ^ FloatFormat.prec.toNat then e_ulp + 1 else e_ulp) +
                    FloatFormat.prec - 1 > FloatFormat.max_exp) := by assumption
              push_neg at this; simp only [show m_rounded ≥ 2 ^ FloatFormat.prec.toNat from hcarry,
                ite_true] at this; omega
            have hval_ne : (mag : R) * (2 : R) ^ e_base ≠ 0 := ne_of_gt hval_pos
            -- roundUp(val) = Fp.finite ⟨false, e_ulp+prec, 2^(prec-1).toNat, _⟩
            have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
              hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
              he_stored_carry (by omega) h_e_ulp_eq
            -- Bridge (prec-1).toNat = prec.toNat - 1 in the result
            have hm_bridge : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
              rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
            -- Simplify the result: m_rounded/2 = 2^(prec.toNat-1), exponent = e_ulp + prec
            simp only [hm_div, show e_ulp + 1 + FloatFormat.prec - 1 = e_ulp + FloatFormat.prec
              from by omega]
            -- Dispatch by sign × mode
            have hru_val : shouldRoundUp mode sign q r shift_nat = true := by
              rw [← hroundup_def]; exact hru
            have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
            -- Factor nearest-mode proofs before cases sign
            have h_TE_round (hm : mode = .NearestTiesToEven) :
                roundNearestTiesToEven ((mag : R) * (2 : R) ^ e_base) =
                roundUp ((mag : R) * (2 : R) ^ e_base) := by
              subst hm
              have hru_te : shouldRoundUp .NearestTiesToEven sign q r shift_nat = true := hru_val
              unfold shouldRoundUp at hru_te
              simp only [show r ≠ 0 from by omega, ↓reduceIte,
                show 2 ^ (shift_nat - 1) = half from rfl] at hru_te
              by_cases hr_gt : r > half
              · exact rnEven_above_mid_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_carry (hmid_unfold _ (carry_float_toVal (R := R) q e_ulp (by omega) _ rfl rfl rfl)) (hr_gt_mid hr_gt)
              · have hr_eq : r = half := by
                  by_contra h_ne; have hlt : r < half := by omega
                  simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_te
                  exact absurd hru_te (by decide)
                have hq_odd : q % 2 ≠ 0 := by
                  simp only [show ¬(r > half) from hr_gt, ite_false,
                    show ¬(r < half) from by omega, ite_false] at hru_te
                  revert hru_te; simp [decide_eq_true_eq]
                exact rnEven_at_mid_odd_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_carry (hmid_unfold _ (carry_float_toVal (R := R) q e_ulp (by omega) _ rfl rfl rfl)) (hr_eq_mid hr_eq)
                    (by rw [hpred_even]; simp [hq_odd])
            have h_TA_round (hm : mode = .NearestTiesAwayFromZero) :
                roundNearestTiesAwayFromZero ((mag : R) * (2 : R) ^ e_base) =
                roundUp ((mag : R) * (2 : R) ^ e_base) := by
              subst hm
              have hru_ta : shouldRoundUp .NearestTiesAwayFromZero sign q r shift_nat = true := hru_val
              unfold shouldRoundUp at hru_ta
              simp only [show r ≠ 0 from by omega, ↓reduceIte,
                show 2 ^ (shift_nat - 1) = half from rfl] at hru_ta
              have hge_half : r ≥ half := by revert hru_ta; simp [decide_eq_true_eq, Nat.not_lt]
              exact rnAway_ge_mid_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                  hroundDown_eq hroundUp_carry (hmid_unfold _ (carry_float_toVal (R := R) q e_ulp (by omega) _ rfl rfl rfl))
                  (by rcases Nat.eq_or_lt_of_le hge_half with h | h
                      · exact (hr_eq_mid h.symm).ge
                      · exact le_of_lt (hr_gt_mid h))
            cases sign
            · -- sign = false
              simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · simp at hru_val  -- Down: impossible
              · simp only [hm_bridge.symm]; exact hroundUp_carry.symm  -- Up
              · simp at hru_val  -- TowardZero: impossible
              · simp only [hm_bridge.symm]; rw [h_TE_round rfl]; exact hroundUp_carry.symm  -- TE
              · simp only [hm_bridge.symm]; rw [h_TA_round rfl]; exact hroundUp_carry.symm  -- TA
            · -- sign = true
              simp only [intSigVal, Bool.true_eq_false, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · -- Down: roundDown(-val) = -(roundUp(val))
                simp only [hm_bridge.symm]
                rw [neg_mul, roundDown_neg_eq_neg_roundUp _ hval_ne,
                    hroundUp_carry, Fp.neg_finite]; simp [FiniteFp.neg_def]
              · simp at hru_val  -- Up: impossible
              · simp at hru_val  -- TowardZero: impossible
              · -- NearestTiesToEven: use rnEven_neg_eq_neg + factored proof
                simp only [hm_bridge.symm]
                rw [neg_mul, rnEven_neg_eq_neg _ hval_ne, h_TE_round rfl,
                    hroundUp_carry, Fp.neg_finite]; simp [FiniteFp.neg_def]
              · -- NearestTiesAwayFromZero: use rnAway_neg_eq_neg + factored proof
                simp only [hm_bridge.symm]
                rw [neg_mul, rnAway_neg_eq_neg _ hval_ne, h_TA_round rfl,
                    hroundUp_carry, Fp.neg_finite]; simp [FiniteFp.neg_def]
          · -- NO-CARRY CASE: q + 1 < 2^prec
            push_neg at hcarry
            have hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat := by omega
            have hno_carry_m : ¬(m_rounded ≥ 2 ^ FloatFormat.prec.toNat) := by omega
            have hno_carry_q1 : ¬(q + 1 ≥ 2 ^ FloatFormat.prec.toNat) := by omega
            simp only [hno_carry_m, hm_eq, hno_carry_q1, if_false, ite_false, ↓reduceIte]
            -- Goal: Fp.finite ⟨sign, e_ulp+prec-1, q+1, _⟩ = mode.round(intSigVal sign mag e_base)
            -- This is the roundUp direction. For sign=false, roundUp(val) gives q+1.
            -- For sign=true, -(roundUp(val)) = roundDown(-val) gives q+1.
            have hval_ne : (mag : R) * (2 : R) ^ e_base ≠ 0 := ne_of_gt hval_pos
            -- roundUp(val) = Fp.finite ⟨false, e_ulp+prec-1, q+1, _⟩
            have hroundUp_eq : roundUp ((mag : R) * (2 : R) ^ e_base) =
                Fp.finite ⟨false, e_ulp + FloatFormat.prec - 1, q + 1, _⟩ :=
              roundUp_nat_mul_zpow mag e_base e_ulp q hmag hval_pos hval_lt_overflow
                hceil_bridge hint_log (by omega) he_stored_le_inner hq1_bound h_e_ulp_eq
            -- Dispatch by sign × mode
            have hru_val : shouldRoundUp mode sign q r shift_nat = true := by
              rw [← hroundup_def]; exact hru
            have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
            -- Factor nearest-mode proofs before cases sign
            have h_TE_round (hm : mode = .NearestTiesToEven) :
                roundNearestTiesToEven ((mag : R) * (2 : R) ^ e_base) =
                roundUp ((mag : R) * (2 : R) ^ e_base) := by
              subst hm
              have hru_te : shouldRoundUp .NearestTiesToEven sign q r shift_nat = true := hru_val
              unfold shouldRoundUp at hru_te
              simp only [show r ≠ 0 from by omega, ↓reduceIte,
                show 2 ^ (shift_nat - 1) = half from rfl] at hru_te
              by_cases hr_gt : r > half
              · exact rnEven_above_mid_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_eq (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl)) (hr_gt_mid hr_gt)
              · have hr_eq : r = half := by
                  by_contra h_ne; have hlt : r < half := by omega
                  simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_te
                  exact absurd hru_te (by decide)
                have hq_odd : q % 2 ≠ 0 := by
                  simp only [show ¬(r > half) from hr_gt, ite_false,
                    show ¬(r < half) from by omega, ite_false] at hru_te
                  revert hru_te; simp [decide_eq_true_eq]
                exact rnEven_at_mid_odd_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_eq (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl)) (hr_eq_mid hr_eq)
                    (by rw [hpred_even]; simp [hq_odd])
            have h_TA_round (hm : mode = .NearestTiesAwayFromZero) :
                roundNearestTiesAwayFromZero ((mag : R) * (2 : R) ^ e_base) =
                roundUp ((mag : R) * (2 : R) ^ e_base) := by
              subst hm
              have hru_ta : shouldRoundUp .NearestTiesAwayFromZero sign q r shift_nat = true := hru_val
              unfold shouldRoundUp at hru_ta
              simp only [show r ≠ 0 from by omega, ↓reduceIte,
                show 2 ^ (shift_nat - 1) = half from rfl] at hru_ta
              have hge_half : r ≥ half := by revert hru_ta; simp [decide_eq_true_eq, Nat.not_lt]
              exact rnAway_ge_mid_roundUp _ mid_val pred_fp _ hval_pos hval_lt_thresh
                  hroundDown_eq hroundUp_eq (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl))
                  (by rcases Nat.eq_or_lt_of_le hge_half with h | h
                      · exact (hr_eq_mid h.symm).ge
                      · exact le_of_lt (hr_gt_mid h))
            cases sign
            · -- sign = false
              simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · simp at hru_val  -- Down: impossible
              · exact hroundUp_eq.symm  -- Up
              · simp at hru_val  -- TowardZero: impossible
              · rw [h_TE_round rfl]; exact hroundUp_eq.symm  -- NearestTiesToEven
              · rw [h_TA_round rfl]; exact hroundUp_eq.symm  -- NearestTiesAwayFromZero
            · -- sign = true
              simp only [intSigVal, Bool.true_eq_false, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · -- Down
                rw [neg_mul, roundDown_neg_eq_neg_roundUp _ hval_ne,
                    hroundUp_eq, Fp.neg_finite]; simp [FiniteFp.neg_def]
              · simp at hru_val  -- Up: impossible
              · simp at hru_val  -- TowardZero: impossible
              · -- NearestTiesToEven: use rnEven_neg_eq_neg + factored proof
                rw [neg_mul, rnEven_neg_eq_neg _ hval_ne, h_TE_round rfl,
                    hroundUp_eq, Fp.neg_finite]; simp [FiniteFp.neg_def]
              · -- NearestTiesAwayFromZero: use rnAway_neg_eq_neg + factored proof
                rw [neg_mul, rnAway_neg_eq_neg _ hval_ne, h_TA_round rfl,
                    hroundUp_eq, Fp.neg_finite]; simp [FiniteFp.neg_def]
        · -- shouldRoundUp = false → m_rounded = q → roundDown direction
          simp only [Bool.not_eq_true] at hru
          have hm_eq : m_rounded = q := by rw [hm_rounded_def]; simp [hru]
          have hno_carry : ¬(m_rounded ≥ 2 ^ FloatFormat.prec.toNat) := by omega
          have hno_carry_q : ¬(q ≥ 2 ^ FloatFormat.prec.toNat) := by omega
          simp only [hno_carry, hm_eq, hno_carry_q, if_false, ite_false, ↓reduceIte]
          -- Goal: Fp.finite ⟨sign, e_ulp+prec-1, q, _⟩ = mode.round(intSigVal sign mag e_base)
          -- The LHS matches roundDown(|val|) with sign, and shouldRoundUp=false means
          -- the mode picks this direction.
          have hru_val : shouldRoundUp mode sign q r shift_nat = false := by rw [← hroundup_def]; exact hru
          have hval_ne : (mag : R) * (2 : R) ^ e_base ≠ 0 := ne_of_gt hval_pos
          -- Factor nearest-mode proofs before cases sign
          -- (shouldRoundUp ignores sign for TE/TA, so the proof is the same)
          have h_TE_round :
              mode = .NearestTiesToEven →
              roundNearestTiesToEven ((mag : R) * (2 : R) ^ e_base) = Fp.finite pred_fp := by
            intro hm; subst hm
            -- Extract TE-specific condition from shouldRoundUp (sign-independent)
            have hru_te : shouldRoundUp .NearestTiesToEven sign q r shift_nat = false := hru_val
            unfold shouldRoundUp at hru_te
            simp only [show r ≠ 0 from by omega, ↓reduceIte,
              show 2 ^ (shift_nat - 1) = half from rfl] at hru_te
            by_cases hr_lt : r < half
            · -- r < half: val < midpoint → returns pred
              by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
              · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                  hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                  he_stored_le_inner hq1 h_e_ulp_eq
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
                rw [rnEven_below_mid_roundDown _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_eq (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl)) (hr_lt_mid hr_lt)]
                exact hroundDown_eq
              · push_neg at hq1
                have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
                by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
                · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                    hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                    he_carry hq_eq h_e_ulp_eq
                  have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                  rw [rnEven_below_mid_roundDown _ mid_val pred_fp _ hval_pos hval_lt_thresh
                      hroundDown_eq hroundUp_carry (hmid_unfold _ (carry_float_toVal (R := R) q e_ulp hq_eq _ rfl rfl rfl)) (hr_lt_mid hr_lt)]
                  exact hroundDown_eq
                · push_neg at he_carry
                  obtain ⟨_, _, hroundUp_inf⟩ :=
                    carry_overflow_pred_lff_roundUp_inf (R := R) mag e_base e_ulp q r hq_eq
                      he_stored_le_inner (by omega) hval_pos hval_decomp hr_pos pred_fp
                      (by rw [hpred_fp_def]) (by rw [hpred_fp_def]) (by rw [hpred_fp_def])
                  have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                      (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                      (2 : R) ^ FloatFormat.max_exp := by
                    linarith [hr_lt_mid hr_lt,
                      (mid_val_eq_overflow_threshold (R := R) q e_ulp (by omega) (by omega)).symm
                        ▸ hmid_val_def]
                  exact rnEven_pos_succ_overflow _ pred_fp hval_pos                    hval_lt_thresh hroundDown_eq hroundUp_inf
            · -- r ≥ half: r = half ∧ q even → at midpoint, pred is even → returns pred
              have hr_not_gt : ¬(r > half) := by
                intro h; simp only [h, ite_true] at hru_te; exact absurd hru_te (by decide)
              have hr_eq : r = half := by omega
              have hq_even : q % 2 = 0 := by
                simp only [hr_not_gt, ite_false, show ¬(r < half) from hr_lt, ite_false] at hru_te
                revert hru_te; simp [decide_eq_false_iff_not, not_not]
              have hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat := by
                by_contra h_ge; push_neg at h_ge
                have hq_max : q = 2 ^ FloatFormat.prec.toNat - 1 := by omega
                have h_dvd : 2 ∣ 2 ^ FloatFormat.prec.toNat :=
                  dvd_pow_self 2 (by have := FloatFormat.valid_prec; omega)
                obtain ⟨k, hk⟩ := h_dvd
                rw [hq_max, hk] at hq_even; omega
              have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                he_stored_le_inner hq1_bound h_e_ulp_eq
              have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
              rw [rnEven_at_mid_even_roundDown _ mid_val pred_fp _ hval_pos hval_lt_thresh
                  hroundDown_eq hroundUp_eq
                  (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl)) (hr_eq_mid hr_eq)
                  (by rw [hpred_even]; simp [hq_even])]
              exact hroundDown_eq
          have h_TA_round :
              mode = .NearestTiesAwayFromZero →
              roundNearestTiesAwayFromZero ((mag : R) * (2 : R) ^ e_base) = Fp.finite pred_fp := by
            intro hm; subst hm
            -- Extract TA-specific condition: r < half (sign-independent)
            have hru_ta : shouldRoundUp .NearestTiesAwayFromZero sign q r shift_nat = false := hru_val
            unfold shouldRoundUp at hru_ta
            simp only [show r ≠ 0 from by omega, ↓reduceIte,
              show 2 ^ (shift_nat - 1) = half from rfl] at hru_ta
            have hr_lt : r < half := by revert hru_ta; simp [decide_eq_false_iff_not, Nat.not_le]
            by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
            · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                he_stored_le_inner hq1 h_e_ulp_eq
              have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
              rw [rnAway_lt_mid_roundDown _ mid_val pred_fp _ hval_pos hval_lt_thresh
                  hroundDown_eq hroundUp_eq (hmid_unfold _ (no_carry_succ_toVal (R := R) q e_ulp _ rfl rfl rfl)) (hr_lt_mid hr_lt)]
              exact hroundDown_eq
            · push_neg at hq1
              have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
              by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
              · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                  hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                  he_carry hq_eq h_e_ulp_eq
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                rw [rnAway_lt_mid_roundDown _ mid_val pred_fp _ hval_pos hval_lt_thresh
                    hroundDown_eq hroundUp_carry (hmid_unfold _ (carry_float_toVal (R := R) q e_ulp hq_eq _ rfl rfl rfl)) (hr_lt_mid hr_lt)]
                exact hroundDown_eq
              · push_neg at he_carry
                obtain ⟨_, _, hroundUp_inf⟩ :=
                  carry_overflow_pred_lff_roundUp_inf (R := R) mag e_base e_ulp q r hq_eq
                    he_stored_le_inner (by omega) hval_pos hval_decomp hr_pos pred_fp
                    (by rw [hpred_fp_def]) (by rw [hpred_fp_def]) (by rw [hpred_fp_def])
                have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                    (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                    (2 : R) ^ FloatFormat.max_exp := by
                  linarith [hr_lt_mid hr_lt,
                    (mid_val_eq_overflow_threshold (R := R) q e_ulp (by omega) (by omega)).symm
                      ▸ hmid_val_def]
                exact rnAway_pos_succ_overflow _ pred_fp hval_pos                  hval_lt_thresh hroundDown_eq hroundUp_inf
          -- Dispatch by sign × mode.
          cases sign
          · -- sign = false
            simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
            unfold shouldRoundUp at hru_val
            simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
            cases mode <;>
              simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
            · exact hroundDown_eq.symm  -- Down
            · simp at hru_val  -- Up: impossible
            · rw [roundTowardZero_pos_eq _ hval_pos]; exact hroundDown_eq.symm  -- TowardZero
            · exact (h_TE_round rfl).symm  -- NearestTiesToEven
            · exact (h_TA_round rfl).symm  -- NearestTiesAwayFromZero
          · -- sign = true
            simp only [intSigVal, Bool.true_eq_false, ↓reduceIte]
            unfold shouldRoundUp at hru_val
            simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
            cases mode <;>
              simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
            · simp at hru_val  -- Down: impossible
            · -- Up: roundUp(-val) = -(roundDown(val))
              rw [neg_mul, roundUp_neg_eq_neg_roundDown _ hval_ne,
                  hroundDown_eq, Fp.neg_finite]; simp [FiniteFp.neg_def, hpred_fp_def]
            · -- TowardZero
              have hneg_val : -(↑mag : R) * (2:R) ^ e_base < 0 := by
                rw [neg_mul]; exact neg_neg_of_pos hval_pos
              rw [roundTowardZero_neg_eq _ hneg_val,
                  neg_mul, roundUp_neg_eq_neg_roundDown _ hval_ne,
                  hroundDown_eq, Fp.neg_finite]; simp [FiniteFp.neg_def, hpred_fp_def]
            · -- NearestTiesToEven: use rnEven_neg_eq_neg + factored proof
              rw [neg_mul, rnEven_neg_eq_neg _ hval_ne, h_TE_round rfl, Fp.neg_finite]
              simp [FiniteFp.neg_def, hpred_fp_def]
            · -- NearestTiesAwayFromZero: use rnAway_neg_eq_neg + factored proof
              rw [neg_mul, rnAway_neg_eq_neg _ hval_ne, h_TA_round rfl, Fp.neg_finite]
              simp [FiniteFp.neg_def, hpred_fp_def]

end roundIntSig_correctness

/-! ## Sticky-Bit Rounding Lemma

When an operation computes an integer quotient `q` with nonzero remainder (Euclidean division
for Div, integer sqrt for Sqrt), the standard technique is to form `mag = 2*q + 1` (odd,
with sticky LSB) and feed it to `roundIntSig`. This theorem packages the common proof that
the sticky value rounds identically to the exact value, handling both sign cases. -/

/-- Sticky-bit rounding correctness: when `q ≥ 2^(prec+2)` and `|exact_val|` lies in
    the open interval `(2q · 2^e_base, 2(q+1) · 2^e_base)`, then
    `roundIntSig mode sign (2*q+1) e_base = mode.round (±|exact_val|)`.

    This factors the shared scaffolding from Div and Sqrt's sticky cases:
    odd-interval argument, `round_eq_on_odd_interval`, and sign dispatch. -/
theorem sticky_roundIntSig_eq_round {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (sign : Bool) (q : ℕ) (e_base : ℤ)
    (hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q)
    (abs_exact : R)
    (he_lo : (2 * (q : R)) * (2 : R) ^ e_base < abs_exact)
    (he_hi : abs_exact < (2 * ((q : R) + 1)) * (2 : R) ^ e_base) :
    roundIntSig mode sign (2 * q + 1) e_base =
      mode.round (if sign then -abs_exact else abs_exact) := by
  set mag := 2 * q + 1 with hmag_def
  set E := (2 : R) ^ e_base with hE_def
  have hE_pos : (0 : R) < E := zpow_pos (by norm_num : (0:R) < 2) _
  -- mag is odd and large
  have hmag_ne : mag ≠ 0 := by omega
  have hmag_odd : mag % 2 = 1 := by omega
  have hmag_large : 2 ^ (FloatFormat.prec.toNat + 3) < mag := by
    have : 2 ^ (FloatFormat.prec.toNat + 3) = 2 * 2 ^ (FloatFormat.prec.toNat + 2) := by
      rw [Nat.pow_succ]; ring
    omega
  -- Apply roundIntSig_correct to get mode.round(intSigVal sign mag e_base)
  rw [roundIntSig_correct (R := R) mode _ _ _ hmag_ne]
  -- Sticky value = ±(mag * E), trivially in the odd interval
  set abs_sticky := (mag : R) * E with habs_sticky_def
  have hs_lo : ((mag : ℤ) - 1 : R) * E < abs_sticky := by
    apply mul_lt_mul_of_pos_right _ hE_pos
    exact_mod_cast (show (mag : ℤ) - 1 < mag from by omega)
  have hs_hi : abs_sticky < ((mag : ℤ) + 1 : R) * E := by
    apply mul_lt_mul_of_pos_right _ hE_pos
    exact_mod_cast (show (mag : ℤ) < mag + 1 from by omega)
  -- Convert caller's q-based bounds to (mag-1)*E / (mag+1)*E form
  have he_lo' : ((mag : ℤ) - 1 : R) * E < abs_exact := by
    have : ((mag : ℤ) - 1 : R) * E = (2 * (q : R)) * E := by
      rw [hmag_def]; push_cast; ring
    rw [this]; exact he_lo
  have he_hi' : abs_exact < ((mag : ℤ) + 1 : R) * E := by
    have : ((mag : ℤ) + 1 : R) * E = (2 * ((q : R) + 1)) * E := by
      rw [hmag_def]; push_cast; ring
    rw [this]; exact he_hi
  -- Positive rounding equality via round_eq_on_odd_interval
  have hround_pos : ∀ m : RoundingMode, m.round abs_sticky = m.round abs_exact :=
    fun m => round_eq_on_odd_interval m hmag_odd hmag_large hs_lo hs_hi he_lo' he_hi'
  -- Positivity (needed for round_neg in sign=true case)
  have hq_ge_one : 1 ≤ q := le_trans Nat.one_le_two_pow hq_lower
  have hlo_E_pos : (0 : R) < ((mag : ℤ) - 1 : R) * E :=
    mul_pos (by exact_mod_cast (show (0 : ℤ) < (mag : ℤ) - 1 from by omega)) hE_pos
  have habs_sticky_ne : abs_sticky ≠ 0 := ne_of_gt (lt_trans hlo_E_pos hs_lo)
  have habs_exact_ne : abs_exact ≠ 0 := ne_of_gt (lt_trans hlo_E_pos he_lo')
  -- Sign dispatch
  cases sign with
  | false =>
    have hsv : intSigVal (R := R) false mag e_base = abs_sticky := by
      unfold intSigVal; simp [habs_sticky_def, hE_def]
    rw [hsv]; exact hround_pos mode
  | true =>
    simp only [ite_true]
    have hsv : intSigVal (R := R) true mag e_base = -abs_sticky := by
      unfold intSigVal; simp [habs_sticky_def, hE_def]
    rw [hsv, RoundingMode.round_neg mode abs_sticky habs_sticky_ne,
        RoundingMode.round_neg mode abs_exact habs_exact_ne]
    congr 1; exact hround_pos mode.conjugate

end RoundIntSig
