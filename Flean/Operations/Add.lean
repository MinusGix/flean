import Flean.Operations.RoundIntSig

/-! # Floating-Point Addition

Softfloat-style floating-point addition using `roundIntSig` as the rounding primitive.

The algorithm for adding two finite floats:
1. Align exponents to a common base
2. Compute the signed integer sum of the aligned significands
3. Handle the zero-sum case (IEEE 754 signed zero rules)
4. For nonzero sums, delegate to `roundIntSig`
-/

section Add

variable [FloatFormat]

/-- Add two finite floating-point numbers with the given rounding mode.

The exact sum `a.toVal + b.toVal` equals `sum × 2^(e_min - prec + 1)` where
`sum` is the signed integer sum of the aligned significands. This exact
integer representation is then rounded via `roundIntSig`. -/
def fpAddFinite (mode : RoundingMode) (a b : FiniteFp) : Fp :=
  let e_min := min a.e b.e
  -- Align significands to common exponent e_min - prec + 1
  -- Each significand is shifted left by (its_e - e_min) bits
  let sa : ℤ := (if a.s then -(a.m : ℤ) else (a.m : ℤ)) * 2^(a.e - e_min).toNat
  let sb : ℤ := (if b.s then -(b.m : ℤ) else (b.m : ℤ)) * 2^(b.e - e_min).toNat
  let sum := sa + sb
  if sum = 0 then
    -- IEEE 754 signed zero rules:
    -- If both operands have the same sign, result has that sign
    -- Otherwise, +0 (except in roundDown mode, which gives -0)
    let result_sign : Bool :=
      if a.s = b.s then a.s
      else match mode with
        | .Down => true
        | _ => false
    Fp.finite ⟨result_sign, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  else
    let sign := decide (sum < 0)
    let mag := sum.natAbs
    roundIntSig mode sign mag (e_min - FloatFormat.prec + 1)

/-- IEEE 754 floating-point addition with full special-case handling.

Special cases:
- Any NaN operand produces NaN
- ∞ + ∞ (same sign) = ∞
- ∞ + (-∞) = NaN
- ∞ + finite = ∞
- finite + finite delegates to `fpAddFinite` -/
def fpAdd (mode : RoundingMode) (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | .infinite sx, .infinite sy =>
    if sx = sy then .infinite sx
    else .NaN
  | .infinite s, .finite _ => .infinite s
  | .finite _, .infinite s => .infinite s
  | .finite a, .finite b => fpAddFinite mode a b

/-! ## Commutativity -/

omit [FloatFormat] in
/-- The signed-zero result sign is symmetric in the operand signs -/
private theorem signed_zero_sign_comm (as bs : Bool) (mode : RoundingMode) :
    (if as = bs then as else match mode with | .Down => true | _ => false) =
    (if bs = as then bs else match mode with | .Down => true | _ => false) := by
  cases as <;> cases bs <;> simp

/-- fpAddFinite is commutative -/
theorem fpAddFinite_comm (mode : RoundingMode) (a b : FiniteFp) :
    fpAddFinite mode a b = fpAddFinite mode b a := by
  simp only [fpAddFinite, min_comm a.e b.e, add_comm
    ((if a.s = true then -(a.m : ℤ) else ↑a.m) * 2 ^ (a.e - min b.e a.e).toNat)
    ((if b.s = true then -(b.m : ℤ) else ↑b.m) * 2 ^ (b.e - min b.e a.e).toNat),
    signed_zero_sign_comm a.s b.s mode]

/-- fpAdd is commutative -/
theorem fpAdd_comm (mode : RoundingMode) (x y : Fp) :
    fpAdd mode x y = fpAdd mode y x := by
  cases x with
  | NaN => cases y <;> simp [fpAdd]
  | infinite sx =>
    cases y with
    | NaN => simp [fpAdd]
    | infinite sy =>
      simp only [fpAdd]
      by_cases h : sx = sy
      · simp [h]
      · have h' : ¬(sy = sx) := fun h' => h (h'.symm)
        simp [h, h']
    | finite b => simp [fpAdd]
  | finite a =>
    cases y with
    | NaN => simp [fpAdd]
    | infinite sy => simp [fpAdd]
    | finite b => simp [fpAdd, fpAddFinite_comm]

/-! ## Representation Lemma -/

/-- The signed integer for a single operand, scaled by 2^(e_min - prec + 1), equals toVal.
    For operand `x` with `e_min ≤ x.e`:
    `(if x.s then -x.m else x.m) * 2^(x.e - e_min) * 2^(e_min - prec + 1) = x.toVal` -/
theorem signed_int_mul_zpow_eq_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : FiniteFp) (e_min : ℤ) (he : e_min ≤ x.e) :
    ((if x.s = true then -(x.m : ℤ) else (x.m : ℤ)) * 2^(x.e - e_min).toNat : ℤ) *
      (2 : R)^(e_min - FloatFormat.prec + 1) = (x.toVal : R) := by
  -- Expand toVal
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  -- Both sides have the form sign * m * 2^exponent
  -- LHS: (±m * 2^(e-e_min)) * 2^(e_min-p+1) cast to R
  -- RHS: (if s then -1 else 1) * m * 2^(e-p+1) in R
  -- Key: 2^(e-e_min) * 2^(e_min-p+1) = 2^(e-p+1) since (e-e_min) + (e_min-p+1) = e-p+1
  push_cast
  -- Now convert ↑(2^(x.e - e_min).toNat) to (2:R)^(x.e - e_min)
  have hnn : 0 ≤ x.e - e_min := by omega
  rw [show (x.e - e_min).toNat = (x.e - e_min).toNat from rfl]
  rw [← zpow_natCast (2 : R) (x.e - e_min).toNat]
  rw [Int.toNat_of_nonneg hnn]
  -- Now combine: 2^(x.e - e_min) * 2^(e_min - prec + 1) = 2^(x.e - prec + 1)
  -- Key: 2^(x.e - e_min) * 2^(e_min - prec + 1) = 2^(x.e - prec + 1)
  have hexp : (2 : R) ^ (x.e - e_min) * (2 : R) ^ (e_min - FloatFormat.prec + 1) =
      (2 : R) ^ (x.e - FloatFormat.prec + 1) := by
    rw [two_zpow_mul]; congr 1; omega
  split_ifs with hs <;> (rw [mul_assoc, hexp]; ring)

/-- The integer sum in fpAddFinite exactly represents `a.toVal + b.toVal`.

`(a.toVal : R) + b.toVal = (sa + sb) * (2 : R)^(e_min - prec + 1)`

where `e_min = min a.e b.e`, `sa` and `sb` are the aligned signed integers. -/
theorem fpAddFinite_exact_sum (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : FiniteFp) :
    (a.toVal : R) + b.toVal =
    (((if a.s = true then -(a.m : ℤ) else (a.m : ℤ)) * 2^(a.e - min a.e b.e).toNat +
      (if b.s = true then -(b.m : ℤ) else (b.m : ℤ)) * 2^(b.e - min a.e b.e).toNat : ℤ) : R) *
    (2 : R)^(min a.e b.e - FloatFormat.prec + 1) := by
  rw [Int.cast_add, add_mul]
  rw [← signed_int_mul_zpow_eq_toVal a (min a.e b.e) (min_le_left a.e b.e)]
  rw [← signed_int_mul_zpow_eq_toVal b (min a.e b.e) (min_le_right a.e b.e)]

/-! ## roundIntSig Correctness -/

section roundIntSig_correctness

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- The real value represented by a signed integer `±mag * 2^e_base`. -/
private def intSigVal (sign : Bool) (mag : ℕ) (e_base : ℤ) : R :=
  (if sign then -(mag : R) else (mag : R)) * (2 : R) ^ e_base

omit [FloatFormat] [FloorRing R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Reconstruct the signed integer from sign and natAbs: if `sign = decide (n < 0)` and
    `mag = n.natAbs` for nonzero `n`, then `intSigVal sign mag e_base = n * 2^e_base`. -/
private theorem intSigVal_eq_int_mul {n : ℤ} (hn : n ≠ 0) (e_base : ℤ) :
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

/-- roundNearestTiesToEven of a sufficiently negative value gives negative infinity. -/
private theorem rnEven_neg_overflow (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp) :
    roundNearestTiesToEven (-y) = Fp.infinite true := by
  unfold roundNearestTiesToEven
  have hne : (-y : R) ≠ 0 := by linarith
  have habs_eq : |-y| = y := by rw [abs_neg, abs_of_pos hy_pos]
  have hsmall : ¬(|-y| < (FiniteFp.smallestPosSubnormal.toVal : R) / 2) := by
    rw [habs_eq]
    linarith [calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp :=
          zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ _ := FloatFormat.zpow_max_exp_le_overflow_threshold]
  have hge : |-y| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
    rw [habs_eq]; exact hy_ge
  simp only [hne, hsmall, hge, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  congr 1; exact decide_eq_true (by linarith : -y < 0)

/-- roundNearestTiesAwayFromZero of a sufficiently negative value gives negative infinity. -/
private theorem rnAway_neg_overflow (y : R) (hy_pos : 0 < y)
    (hy_ge : y ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp) :
    roundNearestTiesAwayFromZero (-y) = Fp.infinite true := by
  unfold roundNearestTiesAwayFromZero
  have hne : (-y : R) ≠ 0 := by linarith
  have habs_eq : |-y| = y := by rw [abs_neg, abs_of_pos hy_pos]
  have hsmall : ¬(|-y| < (FiniteFp.smallestPosSubnormal.toVal : R) / 2) := by
    rw [habs_eq]
    linarith [calc (FiniteFp.smallestPosSubnormal.toVal : R) / 2
        < (2 : R) ^ FloatFormat.min_exp := FiniteFp.smallestPosSubnormal_half_lt_zpow_min_exp
      _ < (2 : R) ^ FloatFormat.max_exp :=
          zpow_lt_zpow_right₀ (by norm_num) FloatFormat.exp_order
      _ ≤ _ := FloatFormat.zpow_max_exp_le_overflow_threshold]
  have hge : |-y| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
    rw [habs_eq]; exact hy_ge
  simp only [hne, hsmall, hge, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  congr 1; exact decide_eq_true (by linarith : -y < 0)

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
  have hthresh_le : (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp ≤
      (2 : R) ^ (FloatFormat.max_exp + 1) := by
    rw [show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring,
        ← two_zpow_mul, zpow_one]
    nlinarith [zpow_pos (by norm_num : (0:R) < 2) FloatFormat.max_exp,
              show (0:R) < 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2 from by positivity]
  have hmag_ge_thresh : (mag : R) * (2 : R) ^ e_base ≥
      (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp :=
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
private theorem round_idempotent (mode : RoundingMode) (f : FiniteFp)
    (h : f.s = false ∨ 0 < f.m) :
    mode.round (f.toVal (R := R)) = Fp.finite f := by
  cases mode with
  | Down => exact roundDown_idempotent f h
  | Up => exact roundUp_idempotent f h
  | TowardZero => exact roundTowardZero_idempotent f h
  | NearestTiesToEven => exact roundNearestTiesToEven_idempotent f h
  | NearestTiesAwayFromZero => exact roundNearestTiesAwayFromZero_idempotent f h

/-- `Int.log 2` of a scaled natural number: `Int.log 2 ((mag : R) * 2^e_base) = Nat.log2 mag + e_base`.
This bridges the `Nat.log2` used in `roundIntSig` with the `Int.log 2` used in `findExponentDown`. -/
private theorem int_log_nat_mul_zpow (mag : ℕ) (e_base : ℤ) (hmag : mag ≠ 0) :
    Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base := by
  have hmag_pos : (0 : R) < (mag : R) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmag)
  have hx_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base :=
    mul_pos hmag_pos (zpow_pos (by norm_num : (0:R) < 2) _)
  -- Lower bound: 2^(Nat.log2 mag + e_base) ≤ mag * 2^e_base
  have hle : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤ (mag : R) * (2 : R) ^ e_base := by
    rw [← two_zpow_mul, zpow_natCast]
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num : (0:R) ≤ 2) _)
    rw [← Nat.cast_ofNat, ← Nat.cast_pow]
    exact_mod_cast Nat.log2_self_le hmag
  -- Upper bound: mag * 2^e_base < 2^(Nat.log2 mag + e_base + 1)
  have hlt : (mag : R) * (2 : R) ^ e_base <
      (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base + 1) := by
    have hmag_lt_bits : (mag : R) < (2 : R) ^ ((Nat.log2 mag + 1 : ℕ) : ℤ) := by
      rw [zpow_natCast, ← Nat.cast_ofNat, ← Nat.cast_pow]
      exact_mod_cast @Nat.lt_log2_self mag
    calc (mag : R) * (2 : R) ^ e_base
        < (2 : R) ^ ((Nat.log2 mag + 1 : ℕ) : ℤ) * (2 : R) ^ e_base :=
          mul_lt_mul_of_pos_right hmag_lt_bits (zpow_pos (by norm_num) _)
      _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base + 1) := by
          rw [two_zpow_mul]; congr 1; push_cast; ring
  -- Conclude from characterization of Int.log
  have h1 : (Nat.log2 mag : ℤ) + e_base ≤ Int.log 2 ((mag : R) * (2 : R) ^ e_base) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hx_pos).mp hle
  have h2 : Int.log 2 ((mag : R) * (2 : R) ^ e_base) ≤ (Nat.log2 mag : ℤ) + e_base := by
    by_contra h
    push_neg at h
    have h' : (Nat.log2 mag : ℤ) + e_base + 1 ≤
        Int.log 2 ((mag : R) * (2 : R) ^ e_base) := by omega
    have hle' := (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hx_pos).mpr h'
    -- hle' : ↑2 ^ (...) ≤ mag * 2^e_base, but ↑2 = (2 : R)
    rw [show (↑(2 : ℕ) : R) = (2 : R) from by push_cast; ring] at hle'
    linarith
  omega

/-- Key bridge lemma: `roundDown` of a positive value `mag * 2^e_base` produces a float with
significand `⌊val / 2^e_ulp⌋` and stored exponent `e_ulp + prec - 1`, where `e_ulp` is the
ULP exponent computed by `roundIntSig`. This bridges `roundIntSig`'s Nat division with
`roundDown`'s floor computation.

The hypotheses mirror the non-overflow, inexact case of `roundIntSig`:
- `hmag`: mag ≠ 0
- `hval_pos`: val > 0
- `hval_lt`: val < 2^(max_exp + 1) (non-overflow)
- `hfloor`: the floor of val / 2^e_ulp equals q
- `hint_log`: Int.log 2 val = Nat.log2 mag + e_base
- `he_ulp_ge_sub`: e_ulp ≥ min_exp - prec + 1
- `he_stored_le`: e_ulp + prec - 1 ≤ max_exp
- `hr_pos`: the remainder is positive (inexact)
-/
private theorem roundDown_nat_mul_zpow
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hfloor : ⌊(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌋ = (q : ℤ))
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq_bound : q < 2 ^ FloatFormat.prec.toNat)
    (hq_pos_or_zero : True) -- placeholder, q can be 0
    (h_e_ulp_eq_normal_or_sub : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundDown ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite ⟨false, e_ulp + FloatFormat.prec - 1, q,
        ⟨by omega, by omega, hq_bound, by
          -- Need: isNormal q ∨ isSubnormal (e_ulp + prec - 1) q
          by_cases hn : 2 ^ (FloatFormat.prec - 1).toNat ≤ q
          · left; exact ⟨hn, hq_bound⟩
          · right
            push_neg at hn
            constructor
            · -- e_ulp + prec - 1 = min_exp when subnormal
              -- If e_ulp > min_exp - prec + 1, then e_ulp = e_base + bits - prec (normal dominates)
              -- In normal case, q ≥ 2^(prec-1) (from floor of a normal value), contradicting hn.
              -- So e_ulp = min_exp - prec + 1 and stored exp = min_exp.
              by_contra h_ne
              have h_gt : e_ulp + FloatFormat.prec - 1 > FloatFormat.min_exp := by omega
              -- This means the normal branch dominates
              have h_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
                rw [h_e_ulp_eq_normal_or_sub]; apply max_eq_left; omega
              -- In normal case, q ≥ 2^(prec-1): from hfloor and the properties of Int.log
              -- val / 2^e_ulp = val / 2^(e - prec + 1) where e = Int.log 2 val
              -- val ≥ 2^e, so val / 2^(e-prec+1) ≥ 2^(prec-1)
              -- Thus ⌊val / 2^e_ulp⌋ ≥ 2^(prec-1)
              have he_eq : e_ulp = (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 := by
                push_cast at h_normal ⊢; omega
              have hval_ge_binade : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤
                  (mag : R) * (2 : R) ^ e_base := by
                rw [← two_zpow_mul, zpow_natCast]
                apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num) _)
                rw [← Nat.cast_ofNat, ← Nat.cast_pow]
                exact_mod_cast Nat.log2_self_le hmag
              have hq_ge_prec : (2 : R) ^ (FloatFormat.prec - 1) ≤
                  (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
                rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
                calc (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp
                    = (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by rw [two_zpow_mul]
                  _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) := by
                      congr 1; rw [he_eq]; ring
                  _ ≤ (mag : R) * (2 : R) ^ e_base := hval_ge_binade
              have : (q : ℤ) ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
                rw [← hfloor]
                exact Int.le_floor.mpr (by
                  push_cast
                  rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
                    FloatFormat.prec_sub_one_toNat_eq]
                  exact hq_ge_prec)
              have hq_ge_nat : 2 ^ (FloatFormat.prec - 1).toNat ≤ q := by
                zify at hn ⊢; exact this
              omega
            · omega⟩⟩ := by
  unfold roundDown findPredecessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findPredecessorPos
  -- Case split on subnormal vs normal vs overflow
  by_cases h_sub : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ FloatFormat.min_exp
  · -- SUBNORMAL CASE
    simp [h_sub]
    -- roundSubnormalDown computes ⌊val / 2^(min_exp - prec + 1)⌋
    -- and e_ulp = min_exp - prec + 1 (subnormal dominates)
    unfold roundSubnormalDown
    -- Need: e_ulp = min_exp - prec + 1 in subnormal case
    -- Since val < 2^min_exp, Int.log 2 val < min_exp
    -- So e_base + bits - prec < min_exp - prec + 1, meaning subnormal dominates
    have he_ulp_sub : e_ulp = FloatFormat.min_exp - FloatFormat.prec + 1 := by
      rw [h_e_ulp_eq_normal_or_sub]
      apply max_eq_right
      -- Need: e_base + bits - prec ≤ min_exp - prec + 1
      -- i.e., e_base + bits ≤ min_exp + 1
      -- From hint_log: Int.log 2 val = Nat.log2 mag + e_base
      -- From val < 2^min_exp: Int.log 2 val < min_exp
      have h_log_lt : (Nat.log2 mag : ℤ) + e_base < FloatFormat.min_exp := by
        rw [← hint_log]
        exact (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2:ℕ)) hval_pos).mp
          (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
      omega
    -- The floor computation: ⌊val / 2^(min_exp - prec + 1)⌋ = q
    have hfloor_sub : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = (q : ℤ) := by
      rw [← he_ulp_sub]; exact hfloor
    -- Need to match FiniteFp.mk equality
    -- roundSubnormalDown returns ⟨false, min_exp, k.natAbs⟩ where k = ⌊val / ulp⌋
    -- We need to show this equals ⟨false, e_ulp + prec - 1, q⟩
    -- Since e_ulp + prec - 1 = (min_exp - prec + 1) + prec - 1 = min_exp ✓
    -- And k.natAbs = q ✓ (from hfloor_sub: k = (q : ℤ), so k.natAbs = q)
    -- Establish key facts
    have hk_eq : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = (q : ℤ) := hfloor_sub
    have he_stored : e_ulp + FloatFormat.prec - 1 = FloatFormat.min_exp := by rw [he_ulp_sub]; ring
    have hnatabs : (⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋).natAbs = q := by
      rw [hk_eq]; exact Int.natAbs_natCast q
    -- The roundSubnormalDown unfolds to: if k = 0 then 0 else ⟨false, min_exp, k.natAbs, _⟩
    -- We need to show this = ⟨false, e_ulp + prec - 1, q, _⟩
    -- Both k=0 and k≠0 cases yield the same result once we rewrite
    -- Use congr to handle validity proof differences
    by_cases hk0 : ⌊(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌋ = 0
    · -- k = 0 means q = 0
      have hq0 : q = 0 := by exact_mod_cast (show (q : ℤ) = 0 from by rw [← hfloor_sub, hk0])
      simp only [hk0, ↓reduceDIte]
      -- Now goal: Fp.finite 0 = Fp.finite ⟨false, e_ulp + prec - 1, q, _⟩
      -- Goal: Fp.finite 0 = Fp.finite ⟨false, e_ulp + prec - 1, q, _⟩
      -- Both are Fp.finite of the zero FiniteFp
      congr 1
      rw [FiniteFp.eq_def, FiniteFp.zero_def]
      exact ⟨rfl, he_stored.symm, hq0.symm⟩
    · -- k ≠ 0
      simp only [hk0, ↓reduceDIte]
      -- Goal: Fp.finite ⟨false, min_exp, k.natAbs, _⟩ = Fp.finite ⟨false, e_ulp+prec-1, q, _⟩
      -- congr 1 decomposes through Fp.finite and FiniteFp into field goals
      congr 1; exact he_stored.symm
  · -- NOT SUBNORMAL: normal or overflow
    push_neg at h_sub
    by_cases h_normal : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1)
    · -- NORMAL CASE
      simp [not_lt.mpr h_sub, h_normal]
      -- roundNormalDown computes ⌊val / 2^e * 2^(prec-1)⌋ = ⌊val / 2^(e-prec+1)⌋
      -- where e = findExponentDown val
      unfold roundNormalDown
      simp only
      -- findExponentDown val = Int.log 2 val (in normal range, since val ∈ [2^min_exp, 2^(max_exp+1)))
      -- From hint_log: Int.log 2 val = Nat.log2 mag + e_base
      have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨h_sub, h_normal⟩
      have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          (Nat.log2 mag : ℤ) + e_base := by
        rw [findExponentDown_normal _ h_nr, hint_log]
      -- e_ulp = e_base + bits - prec (normal dominates since val ≥ 2^min_exp)
      have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq_normal_or_sub]
        apply max_eq_left
        -- Need: min_exp - prec + 1 ≤ e_base + bits - prec
        -- i.e., min_exp + 1 ≤ e_base + bits
        -- From val ≥ 2^min_exp: Int.log 2 val ≥ min_exp
        have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
          rw [← hint_log]
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
            (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
        omega
      -- findExponentDown val - prec + 1 = e_ulp
      have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
          FloatFormat.prec + 1 = e_ulp := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- The floor via floor_scaled_eq_floor_div_ulp_step
      have hfloor_normal : ⌊(mag : R) * (2 : R) ^ e_base /
          (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1)⌋ = (q : ℤ) := by
        have : (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 = e_ulp := by
          rw [he_ulp_normal]; push_cast; ring
        rw [this]; exact hfloor
      congr 1
      · -- e: findExponentDown val = e_ulp + prec - 1
        rw [h_fed, he_ulp_normal]; push_cast; ring
      · -- m: floor_scaled.natAbs = q
        rw [h_fed, floor_scaled_eq_floor_div_ulp_step, hfloor_normal]
        exact Int.natAbs_natCast q
    · -- OVERFLOW: contradiction with hval_lt
      exfalso; linarith

/-- `roundUp` of a positive value `mag * 2^e_base` produces a float with significand
`⌈val / 2^e_ulp⌉` in the no-carry case (q+1 < 2^prec).

Mirror of `roundDown_nat_mul_zpow` for the ceiling direction. -/
private theorem roundUp_nat_mul_zpow
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (hq1_bound : q + 1 < 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundUp ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite ⟨false, e_ulp + FloatFormat.prec - 1, q + 1,
        ⟨by omega, by omega, hq1_bound, by
          by_cases hn : 2 ^ (FloatFormat.prec - 1).toNat ≤ q + 1
          · left; exact ⟨hn, hq1_bound⟩
          · right; push_neg at hn; constructor
            · by_contra h_ne
              have h_gt : e_ulp + FloatFormat.prec - 1 > FloatFormat.min_exp := by omega
              have h_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
                rw [h_e_ulp_eq]; apply max_eq_left; omega
              have hval_ge_binade : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤
                  (mag : R) * (2 : R) ^ e_base := by
                rw [← two_zpow_mul, zpow_natCast]
                apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num) _)
                rw [← Nat.cast_ofNat, ← Nat.cast_pow]
                exact_mod_cast Nat.log2_self_le hmag
              have he_eq : e_ulp = (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 := by
                push_cast at h_normal ⊢; omega
              have hq_ge_prec : (2 : R) ^ (FloatFormat.prec - 1) ≤
                  (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
                rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
                calc (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp
                    = (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by rw [two_zpow_mul]
                  _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) := by congr 1; rw [he_eq]; ring
                  _ ≤ (mag : R) * (2 : R) ^ e_base := hval_ge_binade
              -- ⌈val / 2^e_ulp⌉ = q + 1, but val / 2^e_ulp ≥ 2^(prec-1), so q + 1 ≥ 2^(prec-1) + 1
              -- Actually q + 1 ≥ 2^(prec-1) since ⌈x⌉ ≥ x
              have hq1_ge_z : (q : ℤ) + 1 ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
                rw [← hceil]
                exact Int.le_ceil_iff.mpr (by
                  push_cast
                  rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
                    FloatFormat.prec_sub_one_toNat_eq]
                  linarith [hq_ge_prec])
              have : 2 ^ (FloatFormat.prec - 1).toNat ≤ q + 1 := by zify; exact hq1_ge_z
              omega
            · omega⟩⟩ := by
  unfold roundUp findSuccessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findSuccessorPos
  by_cases h_sub : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ FloatFormat.min_exp
  · -- SUBNORMAL CASE
    simp [h_sub]
    unfold roundSubnormalUp
    have he_ulp_sub : e_ulp = FloatFormat.min_exp - FloatFormat.prec + 1 := by
      rw [h_e_ulp_eq]; apply max_eq_right
      have h_log_lt : (Nat.log2 mag : ℤ) + e_base < FloatFormat.min_exp := by
        rw [← hint_log]
        exact (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2:ℕ)) hval_pos).mp
          (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
      omega
    have hceil_sub : ⌈(mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)⌉ = (q : ℤ) + 1 := by
      rw [← he_ulp_sub]; exact hceil
    -- val < 2^min_exp and ulp_sub = 2^(min_exp-prec+1), so val/ulp < 2^(prec-1)
    -- ⌈val/ulp⌉ ≤ 2^(prec-1), giving q+1 ≤ 2^(prec-1)
    have hval_div_le : (mag : R) * (2 : R) ^ e_base /
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤
        (2 : R) ^ (FloatFormat.prec - 1) := by
      rw [div_le_iff₀ (zpow_pos (by norm_num : (0:R) < 2) _)]
      have h2 : (2 : R) ^ (FloatFormat.prec - 1) *
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) =
          (2 : R) ^ FloatFormat.min_exp := by
        rw [two_zpow_mul]; congr 1; ring
      rw [h2]; linarith [h_sub]
    have hq1_le_half : (q : ℤ) + 1 ≤ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat := by
      rw [← hceil_sub]
      apply Int.ceil_le.mpr
      push_cast
      rw [← zpow_natCast (2 : R) (FloatFormat.prec - 1).toNat,
          FloatFormat.prec_sub_one_toNat_eq]
      exact hval_div_le
    have he_stored : e_ulp + FloatFormat.prec - 1 = FloatFormat.min_exp := by
      rw [he_ulp_sub]; ring
    simp only [hceil_sub]
    by_cases hk_ge : (q : ℤ) + 1 ≥ (2 : ℤ) ^ (FloatFormat.prec - 1).toNat
    · -- q + 1 = 2^(prec-1): roundSubnormalUp returns smallestPosNormal
      simp only [hk_ge, ↓reduceDIte]
      have hq1_eq : (q : ℤ) + 1 = (2 : ℤ) ^ (FloatFormat.prec - 1).toNat :=
        le_antisymm hq1_le_half hk_ge
      -- smallestPosNormal = ⟨false, min_exp, 2^(prec-1).toNat, _⟩
      -- Our target = ⟨false, e_ulp+prec-1, q+1, _⟩ = ⟨false, min_exp, 2^(prec-1).toNat, _⟩
      unfold FiniteFp.smallestPosNormal
      congr 1
      · exact he_stored.symm
      · -- q + 1 = 2^(prec-1).toNat in ℕ
        have : q + 1 = 2 ^ (FloatFormat.prec - 1).toNat := by
          zify; exact hq1_eq
        omega
    · -- q + 1 < 2^(prec-1): roundSubnormalUp returns ⟨false, min_exp, (q+1).natAbs, _⟩
      simp only [hk_ge, ↓reduceDIte, not_false_eq_true]
      have hnatabs : ((q : ℤ) + 1).natAbs = q + 1 := by
        rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) from by push_cast; ring]
        exact Int.natAbs_natCast (q + 1)
      rw [FiniteFp.eq_def]
      exact ⟨rfl, he_stored.symm, hnatabs⟩
  · -- NOT SUBNORMAL
    push_neg at h_sub
    by_cases h_normal : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1)
    · -- NORMAL CASE
      simp [not_lt.mpr h_sub, h_normal]
      unfold roundNormalUp
      simp only
      have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨h_sub, h_normal⟩
      have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          (Nat.log2 mag : ℤ) + e_base := by
        rw [findExponentDown_normal _ h_nr, hint_log]
      have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
        rw [h_e_ulp_eq]; apply max_eq_left
        have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
          rw [← hint_log]
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
            (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
        omega
      have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
          FloatFormat.prec + 1 = e_ulp := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- The ceil via ceil_scaled_eq_ceil_div_ulp_step
      have hceil_normal : ⌈(mag : R) * (2 : R) ^ e_base /
          (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1)⌉ = (q : ℤ) + 1 := by
        have : (Nat.log2 mag : ℤ) + e_base - FloatFormat.prec + 1 = e_ulp := by
          rw [he_ulp_normal]; push_cast; ring
        rw [this]; exact hceil
      -- The ceil of the scaled value = q + 1
      have hceil_scaled : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ findExponentDown ((mag : R) * (2 : R) ^ e_base) *
          (2 : R) ^ (FloatFormat.prec - 1)⌉ = (q : ℤ) + 1 := by
        rw [ceil_scaled_eq_ceil_div_ulp_step, h_fed_ulp]; exact hceil
      -- No binade overflow: q + 1 < 2^prec
      have hno_binade : ¬((2 : ℤ) ^ FloatFormat.prec.toNat ≤ (q : ℤ) + 1) := by
        push_neg; exact_mod_cast hq1_bound
      simp only [hceil_scaled, hno_binade, ↓reduceDIte]
      have hnatabs : ((q : ℤ) + 1).natAbs = q + 1 := by
        rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) from by push_cast; ring]
        exact Int.natAbs_natCast (q + 1)
      have he_fed_eq_stored : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
          e_ulp + FloatFormat.prec - 1 := by
        rw [h_fed, he_ulp_normal]; push_cast; ring
      -- Goal: Fp.finite ⟨..., findExponentDown(val), (q+1).natAbs, _⟩ = Fp.finite ⟨..., e_ulp+prec-1, q+1, _⟩
      congr 1
      rw [FiniteFp.eq_def]
      exact ⟨rfl, he_fed_eq_stored, hnatabs⟩
    · exfalso; linarith

/-- `roundUp` in the carry case: when `q + 1 = 2^prec`, the ceiling crosses a binade boundary.
The result is `2^(e_ulp+prec)` stored as `⟨false, e_ulp+prec, 2^(prec-1), _⟩`. -/
private theorem roundUp_nat_mul_zpow_carry
    (mag : ℕ) (e_base e_ulp : ℤ) (q : ℕ)
    (hmag : mag ≠ 0)
    (hval_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base)
    (hval_lt : (mag : R) * (2 : R) ^ e_base < (2 : R) ^ (FloatFormat.max_exp + 1))
    (hceil : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ = (q : ℤ) + 1)
    (hint_log : Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base)
    (he_ulp_ge_sub : e_ulp ≥ FloatFormat.min_exp - FloatFormat.prec + 1)
    (he_stored_le : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp)
    (hq1_eq_pow : q + 1 = 2 ^ FloatFormat.prec.toNat)
    (h_e_ulp_eq : e_ulp = max (e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec)
        (FloatFormat.min_exp - FloatFormat.prec + 1)) :
    roundUp ((mag : R) * (2 : R) ^ e_base) =
      Fp.finite ⟨false, e_ulp + FloatFormat.prec, 2 ^ (FloatFormat.prec - 1).toNat,
        ⟨by omega, by omega,
         by have := FloatFormat.valid_prec; exact Nat.pow_lt_pow_right (by norm_num)
              (by omega),
         by left; exact ⟨le_refl _, Nat.pow_lt_pow_right (by norm_num) (by
              have := FloatFormat.valid_prec; omega)⟩⟩⟩ := by
  -- val > q * 2^e_ulp ≥ 2^(prec-1) * 2^(min_exp-prec+1) = 2^min_exp
  have hval_gt_q_ulp : (q : R) * (2 : R) ^ e_ulp < (mag : R) * (2 : R) ^ e_base := by
    -- ⌈val/ulp⌉ = q+1 and q is an integer, so val/ulp > q (since ⌈x⌉ ≥ n+1 means x > n)
    have h_ceil_gt : (q : R) < (mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp := by
      have := Int.lt_ceil.mp (show (q : ℤ) < ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ e_ulp⌉ from
        by rw [hceil]; omega)
      exact_mod_cast this
    rwa [lt_div_iff₀ (zpow_pos (by norm_num : (0:R) < 2) _)] at h_ceil_gt
  have hval_ge_min : (2 : R) ^ FloatFormat.min_exp ≤ (mag : R) * (2 : R) ^ e_base := by
    have hq_ge_half : (2 : R) ^ (FloatFormat.prec - 1) ≤ (q : R) := by
      have hp := FloatFormat.valid_prec
      have hq_nat_ge : 2 ^ (FloatFormat.prec.toNat - 1) ≤ q := by
        have h1 := Nat.one_le_two_pow (n := FloatFormat.prec.toNat - 1)
        have h2 : 2 ^ FloatFormat.prec.toNat = 2 ^ (FloatFormat.prec.toNat - 1 + 1) := by
          congr 1; omega
        rw [pow_succ] at h2
        omega
      -- (2:R)^(prec-1) ≤ (q:R) since 2^(prec.toNat-1) ≤ q in ℕ
      rw [← FloatFormat.pow_toNat_sub_one_eq_zpow_sub_one (R := R)]
      rw [← Nat.cast_ofNat, ← Nat.cast_pow]
      exact_mod_cast hq_nat_ge
    calc (2 : R) ^ FloatFormat.min_exp
        = (2 : R) ^ ((FloatFormat.prec - 1) + (FloatFormat.min_exp - FloatFormat.prec + 1)) := by
          congr 1; ring
      _ ≤ (2 : R) ^ ((FloatFormat.prec - 1) + e_ulp) := by
          apply zpow_le_zpow_right₀ (by norm_num); omega
      _ = (2 : R) ^ (FloatFormat.prec - 1) * (2 : R) ^ e_ulp := by rw [two_zpow_mul]
      _ ≤ (q : R) * (2 : R) ^ e_ulp := by
          apply mul_le_mul_of_nonneg_right hq_ge_half (le_of_lt (zpow_pos (by norm_num) _))
      _ ≤ (mag : R) * (2 : R) ^ e_base := le_of_lt hval_gt_q_ulp
  unfold roundUp findSuccessor
  simp [ne_of_gt hval_pos, hval_pos]
  unfold findSuccessorPos
  simp [not_lt.mpr hval_ge_min, hval_lt]
  -- Now in roundNormalUp
  unfold roundNormalUp
  simp only
  have h_nr : isNormalRange ((mag : R) * (2 : R) ^ e_base) := ⟨hval_ge_min, hval_lt⟩
  have h_fed : findExponentDown ((mag : R) * (2 : R) ^ e_base) =
      (Nat.log2 mag : ℤ) + e_base := by
    rw [findExponentDown_normal _ h_nr, hint_log]
  have he_ulp_normal : e_ulp = e_base + ↑(Nat.log2 mag + 1) - FloatFormat.prec := by
    rw [h_e_ulp_eq]; apply max_eq_left
    have h_log_ge : FloatFormat.min_exp ≤ (Nat.log2 mag : ℤ) + e_base := by
      rw [← hint_log]
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2:ℕ)) hval_pos).mp
        (by rwa [show (↑(2:ℕ) : R) = (2:R) from by push_cast; ring])
    omega
  have h_fed_ulp : findExponentDown ((mag : R) * (2 : R) ^ e_base) -
      FloatFormat.prec + 1 = e_ulp := by
    rw [h_fed, he_ulp_normal]; push_cast; ring
  -- The ceil of the scaled value = q + 1
  have hceil_scaled : ⌈(mag : R) * (2 : R) ^ e_base / (2 : R) ^ findExponentDown ((mag : R) * (2 : R) ^ e_base) *
      (2 : R) ^ (FloatFormat.prec - 1)⌉ = (q : ℤ) + 1 := by
    rw [ceil_scaled_eq_ceil_div_ulp_step, h_fed_ulp]; exact hceil
  -- Binade overflow: q + 1 = 2^prec ≥ 2^prec
  have hbinade : (2 : ℤ) ^ FloatFormat.prec.toNat ≤ (q : ℤ) + 1 := by
    exact_mod_cast (show 2 ^ FloatFormat.prec.toNat ≤ q + 1 from by omega)
  -- Not above max_exp + 1
  have hfed_le_max : findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 ≤ FloatFormat.max_exp := by
    rw [h_fed]
    have : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp := he_stored_le
    rw [he_ulp_normal] at this
    have := FloatFormat.prec_pos; push_cast at this ⊢; omega
  have hno_overflow : ¬(findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 >
      FloatFormat.max_exp) := by
    push_neg; exact hfed_le_max
  simp only [hceil_scaled, hbinade, hno_overflow, ↓reduceDIte, ite_false]
  -- Goal: Fp.finite ⟨false, fed+1, 2^(prec-1).toNat, _⟩ = Fp.finite ⟨false, e_ulp+prec, 2^(prec.toNat-1), _⟩
  have he_eq : findExponentDown ((mag : R) * (2 : R) ^ e_base) + 1 =
      e_ulp + FloatFormat.prec := by
    rw [h_fed, he_ulp_normal]; push_cast; ring
  have hm_eq : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
  simp only [he_eq, hm_eq]

/-! ### Nearest Mode Helpers

These lemmas connect the integer-level midpoint comparison (`r` vs `2^(shift-1)`) with
the real-level nearest rounding functions. -/

/-- For positive `val` in the representable range, if `val < midpoint(pred, succ)` then
`roundNearestTiesToEven(val) = roundDown(val)`, and if `val > midpoint` then
`roundNearestTiesToEven(val) = roundUp(val)`. For the tie case, even parity decides. -/
private theorem rnEven_pos_of_roundDown_roundUp
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp)
    (hmid_lt : val < (pred_fp.toVal + succ_fp.toVal) / 2 →
      roundNearestTiesToEven val = roundDown val)
    (hmid_gt : val > (pred_fp.toVal + succ_fp.toVal) / 2 →
      roundNearestTiesToEven val = roundUp val)
    (hmid_even : val = (pred_fp.toVal + succ_fp.toVal) / 2 → isEvenSignificand pred_fp →
      roundNearestTiesToEven val = roundDown val)
    (hmid_odd : val = (pred_fp.toVal + succ_fp.toVal) / 2 → ¬isEvenSignificand pred_fp →
      roundNearestTiesToEven val = roundUp val) :
    True := trivial  -- This is just documentation; the actual proofs use the cases directly

-- The actual workhorse: unfold roundNearestTiesToEven for positive val in range
private theorem rnEven_pos_unfold
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesToEven val =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val < midpoint then Fp.finite pred_fp
      else if val > midpoint then Fp.finite succ_fp
      else if isEvenSignificand pred_fp then Fp.finite pred_fp
      else Fp.finite succ_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  -- Now in the let/match branch
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  -- roundDown = findPredecessor, roundUp = findSuccessor for positive val
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := by
    exact Fp.finite.inj hpred_eq
  -- findSuccessorPos returns Fp, not FiniteFp. We need to case-match.
  rw [hsucc_eq_fp]
  dsimp only
  rw [hpred_fp_eq]

/-- Similar unfolding for roundNearestTiesAwayFromZero on positive values. -/
private theorem rnAway_pos_unfold
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesAwayFromZero val =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val < midpoint then Fp.finite pred_fp
      else if val > midpoint then Fp.finite succ_fp
      else if val > 0 then Fp.finite succ_fp
      else Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := by
    exact Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp]
  dsimp only
  rw [hpred_fp_eq]

/-- Similar unfolding for roundNearestTiesToEven on negative values (-val where val > 0). -/
private theorem rnEven_neg_unfold
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesToEven (-val) =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val > midpoint then -(Fp.finite succ_fp)
      else if val < midpoint then -(Fp.finite pred_fp)
      else if isEvenSignificand succ_fp then -(Fp.finite succ_fp)
      else -(Fp.finite pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  -- For negative -val: findPredecessor(-val) = -(findSuccessorPos val)
  --                    findSuccessor(-val) = Fp.finite (-(findPredecessorPos val))
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  -- Now findSuccessorPos val and findPredecessorPos val appear
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp, hpred_fp_eq]
  -- Need to reduce -Fp.finite succ_fp to Fp.finite (-succ_fp) for match
  simp only [Fp.neg_finite, FiniteFp.toVal_neg_eq_neg]
  -- Goal now has if-then-else with -val comparisons on LHS, val comparisons on RHS
  -- isEvenSignificand(-succ_fp) = isEvenSignificand(succ_fp)
  have heven_neg : isEvenSignificand (-succ_fp) = isEvenSignificand succ_fp := by
    simp [isEvenSignificand, FiniteFp.neg_def]
  rw [heven_neg]
  -- Split on all conditions and close with linarith
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all <;> linarith

/-- Similar unfolding for roundNearestTiesAwayFromZero on negative values. -/
private theorem rnAway_neg_unfold
    (val : R) (pred_fp succ_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp : roundUp val = Fp.finite succ_fp) :
    roundNearestTiesAwayFromZero (-val) =
      let midpoint := (pred_fp.toVal + succ_fp.toVal) / 2
      if val > midpoint then -(Fp.finite succ_fp)
      else if val < midpoint then -(Fp.finite pred_fp)
      else -(Fp.finite succ_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hpred_eq : Fp.finite (findPredecessorPos val hval_pos) = Fp.finite pred_fp := by
    rw [← findPredecessor_pos_eq val hval_pos, ← hroundDown]; rfl
  have hsucc_eq_fp : findSuccessorPos val hval_pos = Fp.finite succ_fp := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp := Fp.finite.inj hpred_eq
  rw [hsucc_eq_fp, hpred_fp_eq]
  dsimp only
  simp only [Fp.neg_finite, FiniteFp.toVal_neg_eq_neg]
  congr 1
  · ext; constructor
    · intro h; linarith
    · intro h; linarith
  congr 1
  · ext; constructor
    · intro h; linarith
    · intro h; linarith
  -- tie: -val > 0 is false since hval_pos : 0 < val → -val < 0
  have h_neg_not_pos : ¬(-val > 0) := by linarith
  simp [h_neg_not_pos]

private theorem largestFiniteFloat_lt_overflow_threshold :
    FiniteFp.largestFiniteFloat.toVal <
    (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp := by
  rw [FiniteFp.largestFiniteFloat_toVal,
    show -(FloatFormat.prec : ℤ) + 1 = 1 - (FloatFormat.prec : ℤ) from by ring,
    mul_comm ((2:R) - _) _]
  exact mul_lt_mul_of_pos_left
    (by linarith [zpow_pos (by norm_num : (0:R) < 2) (1 - (FloatFormat.prec : ℤ))])
    (zpow_pos (by norm_num : (0:R) < 2) _)

private theorem val_lt_thresh_of_roundUp_finite
    (val : R) (f : FiniteFp) (hval_pos : 0 < val)
    (hroundUp : roundUp val = Fp.finite f) :
    val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp := by
  have hfsp : findSuccessorPos val hval_pos = Fp.finite f := by
    rw [← findSuccessor_pos_eq val hval_pos, ← hroundUp]; rfl
  calc val ≤ f.toVal := findSuccessorPos_ge val hval_pos f hfsp
    _ ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
    _ < _ := largestFiniteFloat_lt_overflow_threshold

/-- When roundUp overflows and val < threshold, roundNearestTiesToEven returns roundDown. -/
private theorem rnEven_pos_succ_overflow
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesToEven val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf]; dsimp only; rw [hpred_fp_eq]

/-- When roundUp overflows and val < threshold, roundNearestTiesAwayFromZero returns roundDown. -/
private theorem rnAway_pos_succ_overflow
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesAwayFromZero val = Fp.finite pred_fp := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have h_not_small : ¬(|val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hval_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_pos_eq val hval_pos, findSuccessor_pos_eq val hval_pos]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf]; dsimp only; rw [hpred_fp_eq]

/-- When roundUp overflows for val > 0 and val < threshold,
    roundNearestTiesToEven(-val) returns Fp.finite (-pred_fp). -/
private theorem rnEven_neg_succ_overflow
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesToEven (-val) = Fp.finite (-pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesToEven
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf, hpred_fp_eq]

/-- When roundUp overflows for val > 0 and val < threshold,
    roundNearestTiesAwayFromZero(-val) returns Fp.finite (-pred_fp). -/
private theorem rnAway_neg_succ_overflow
    (val : R) (pred_fp : FiniteFp)
    (hval_pos : 0 < val)
    (hval_ge_ssps : val ≥ FiniteFp.smallestPosSubnormal.toVal)
    (hval_lt_thresh : val < (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp)
    (hroundDown : roundDown val = Fp.finite pred_fp)
    (hroundUp_inf : roundUp val = Fp.infinite false) :
    roundNearestTiesAwayFromZero (-val) = Fp.finite (-pred_fp) := by
  have hval_ne : val ≠ 0 := ne_of_gt hval_pos
  have hneg_ne : -val ≠ 0 := neg_ne_zero.mpr hval_ne
  have hneg_lt : -val < 0 := neg_lt_zero.mpr hval_pos
  have h_not_small : ¬(|-val| < FiniteFp.smallestPosSubnormal.toVal / 2) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  have h_not_overflow : ¬(|-val| ≥ (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2:R) ^ FloatFormat.max_exp) := by
    rw [abs_neg, abs_of_pos hval_pos]; push_neg; exact hval_lt_thresh
  unfold roundNearestTiesAwayFromZero
  rw [if_neg hneg_ne, if_neg h_not_small, if_neg h_not_overflow]
  simp only [findPredecessor_neg_eq (-val) hneg_lt, findSuccessor_neg_eq (-val) hneg_lt, neg_neg]
  have hsucc_inf : findSuccessorPos val hval_pos = Fp.infinite false := by
    have : roundUp val = findSuccessorPos val hval_pos := by
      show findSuccessor val = _; exact findSuccessor_pos_eq val hval_pos
    rw [this] at hroundUp_inf; exact hroundUp_inf
  have hpred_fp_eq : findPredecessorPos val hval_pos = pred_fp :=
    Fp.finite.inj (by
      have : roundDown val = Fp.finite (findPredecessorPos val hval_pos) := by
        show findPredecessor val = _; exact findPredecessor_pos_eq val hval_pos
      rw [this] at hroundDown; exact hroundDown)
  rw [hsucc_inf, hpred_fp_eq]

set_option maxHeartbeats 800000 in
/-- `roundIntSig` correctly rounds the value `±mag × 2^e_base` according to the given rounding mode.

This is the core correctness theorem: `roundIntSig` is equivalent to `mode.round` applied to the
exact real value it represents. -/
theorem roundIntSig_correct (mode : RoundingMode) (sign : Bool) (mag : ℕ) (e_base : ℤ)
    (hmag : mag ≠ 0)
    (hval_ge_ssps : (mag : R) * (2 : R) ^ e_base ≥ FiniteFp.smallestPosSubnormal.toVal) :
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
              (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp := by
            have hmag_ge_sum : mag ≥ 2 ^ shift_nat * q + 2 ^ (shift_nat - 1) := by omega
            have hmag_ge_r : (mag : R) ≥ (q : R) * (2 : R) ^ (shift_nat : ℕ) + (2 : R) ^ ((shift_nat - 1 : ℕ) : ℤ) := by
              have : (2 ^ shift_nat * q + 2 ^ (shift_nat - 1) : ℕ) ≤ mag := hmag_ge_sum
              have h := (Nat.cast_le (α := R)).mpr this
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
              rw [zpow_natCast]; linarith
            have hshift_ge_one : shift_nat ≥ 1 := by omega
            suffices (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp ≤
                ((q : R) * (2 : R) ^ (shift_nat : ℕ) + (2 : R) ^ ((shift_nat - 1 : ℕ) : ℤ)) * (2 : R) ^ e_base by
              calc (mag : R) * (2:R)^e_base
                  ≥ ((q : R) * (2 : R) ^ (shift_nat : ℕ) + (2 : R) ^ ((shift_nat - 1 : ℕ) : ℤ)) * (2:R)^e_base :=
                    mul_le_mul_of_nonneg_right hmag_ge_r (by positivity)
                _ ≥ _ := this
            have hrhs : ((q : R) * (2 : R) ^ (shift_nat : ℕ) + (2 : R) ^ ((shift_nat - 1 : ℕ) : ℤ)) * (2 : R) ^ e_base =
                (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) := by
              have hexp1 : (2 : R) ^ (shift_nat : ℕ) * (2 : R) ^ e_base = (2 : R) ^ e_ulp := by
                rw [← zpow_natCast (2:R) shift_nat, hshift_nat_eq, two_zpow_mul]
                congr 1; omega
              have hexp2 : (2 : R) ^ ((shift_nat - 1 : ℕ) : ℤ) * (2 : R) ^ e_base = (2 : R) ^ (e_ulp - 1) := by
                rw [two_zpow_mul]; congr 1; omega
              rw [add_mul, mul_assoc, hexp1, hexp2]
            rw [hrhs, he_ulp_eq]
            -- Both sides equal 2^(me+1) - 2^(me-p)
            -- LHS = (2 - 2^(1-p)/2) * 2^me
            -- RHS = q * 2^(me-p+1) + 2^(me-p) = (2^p - 1) * 2^(me-p+1) + 2^(me-p)
            -- Show they're equal by reducing both to the same expression
            suffices h : (2 - 2 ^ (1 - (FloatFormat.prec : ℤ)) / 2) * (2 : R) ^ FloatFormat.max_exp =
                (q : R) * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) + (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1 - 1) by
              exact le_of_eq h
            -- Both sides = 2^(me+1) - 2^(me-p).
            -- We prove this by reducing both to the same expression using zpow arithmetic.
            have hq_cast : (q : R) = (2 : R) ^ FloatFormat.prec - 1 := by
              rw [hq_eq, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
                  ← zpow_natCast (2 : R) FloatFormat.prec.toNat, FloatFormat.prec_toNat_eq]
              simp
            -- Key zpow identities
            have h_step : (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) =
                2 * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec) := by
              rw [show FloatFormat.max_exp - FloatFormat.prec + 1 = 1 + (FloatFormat.max_exp - FloatFormat.prec) from by ring,
                  ← two_zpow_mul, zpow_one]
            have h_prec_step : (2 : R) ^ FloatFormat.prec * (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec + 1) =
                2 * (2 : R) ^ FloatFormat.max_exp := by
              rw [two_zpow_mul,
                  show FloatFormat.prec + (FloatFormat.max_exp - FloatFormat.prec + 1) = FloatFormat.max_exp + 1 from by ring,
                  show FloatFormat.max_exp + 1 = 1 + FloatFormat.max_exp from by ring,
                  ← two_zpow_mul, zpow_one]
            have h_eps : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2 * (2 : R) ^ FloatFormat.max_exp =
                (2 : R) ^ (FloatFormat.max_exp - FloatFormat.prec) := by
              rw [div_mul_eq_mul_div, two_zpow_mul,
                  show 1 - FloatFormat.prec + FloatFormat.max_exp = FloatFormat.max_exp - FloatFormat.prec + 1 from by ring,
                  h_step, mul_div_cancel_left₀ _ (two_ne_zero)]
            -- Bridge: me-p+1-1 = me-p
            have h_exp_eq : FloatFormat.max_exp - FloatFormat.prec + 1 - 1 = FloatFormat.max_exp - FloatFormat.prec := by ring
            rw [h_exp_eq]
            -- Expand LHS
            rw [sub_mul, h_eps]
            -- Expand RHS
            rw [hq_cast, sub_mul, one_mul, h_prec_step, h_step]
            ring
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
            cases sign
            · -- sign = false
              simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · simp at hru_val  -- Down: impossible
              · -- Up: roundUp(val) = result
                simp only [hm_bridge.symm]
                exact hroundUp_carry.symm
              · simp at hru_val  -- TowardZero: impossible
              · -- NearestTiesToEven (carry, sign=false, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                simp only [hm_bridge.symm]
                rw [rnEven_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_carry]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul]
                  rw [hm_bridge,
                      show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                        from by omega]
                  push_cast
                  rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                        exact_mod_cast (show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega),
                      ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                      ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                      two_zpow_mul, two_zpow_mul]
                  congr 1
                  rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                        have := FloatFormat.valid_prec; omega)]
                  omega)]
                by_cases hr_gt : r > half
                · rw [if_neg (not_lt.mpr (le_of_lt (hr_gt_mid hr_gt))),
                      if_pos (hr_gt_mid hr_gt)]
                · have hr_eq : r = half := by
                    by_contra h_ne; have hlt : r < half := by omega
                    simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_val
                    exact absurd hru_val (by decide)
                  rw [if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge),
                      if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le)]
                  have hq_odd : q % 2 ≠ 0 := by
                    simp only [show ¬(r > half) from hr_gt, ite_false,
                      show ¬(r < half) from by omega, ite_false] at hru_val
                    revert hru_val; simp [decide_eq_true_eq]
                  rw [hpred_even, show decide (q % 2 = 0) = false from by simp [hq_odd]]; simp
              · -- NearestTiesAwayFromZero (carry, sign=false, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                simp only [hm_bridge.symm]
                rw [rnAway_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_carry]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul]
                  rw [hm_bridge,
                      show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                        from by omega]
                  push_cast
                  rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                        exact_mod_cast (show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega),
                      ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                      ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                      two_zpow_mul, two_zpow_mul]
                  congr 1
                  rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                        have := FloatFormat.valid_prec; omega)]
                  omega)]
                have hge_half : r ≥ half := by
                  revert hru_val; simp [decide_eq_true_eq, Nat.not_lt]
                by_cases hr_gt : r > half
                · rw [if_neg (not_lt.mpr (le_of_lt (hr_gt_mid hr_gt))),
                      if_pos (hr_gt_mid hr_gt)]
                · have hr_eq : r = half := by omega
                  rw [if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge),
                      if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_pos hval_pos]
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
              · -- NearestTiesToEven (carry, sign=true, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                simp only [hm_bridge.symm]
                rw [neg_mul, rnEven_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_carry]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul]
                  rw [hm_bridge,
                      show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                        from by omega]
                  push_cast
                  rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                        exact_mod_cast (show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega),
                      ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                      ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                      two_zpow_mul, two_zpow_mul]
                  congr 1
                  rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                        have := FloatFormat.valid_prec; omega)]
                  omega)]
                by_cases hr_gt : r > half
                · rw [if_pos (hr_gt_mid hr_gt), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
                · have hr_eq : r = half := by
                    by_contra h_ne; have hlt : r < half := by omega
                    simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_val
                    exact absurd hru_val (by decide)
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge)]
                  -- q odd → q+1=2^prec → succ m = 2^(prec-1) which is even (prec ≥ 2)
                  have hq_odd : q % 2 ≠ 0 := by
                    simp only [show ¬(r > half) from hr_gt, ite_false,
                      show ¬(r < half) from by omega, ite_false] at hru_val
                    revert hru_val; simp [decide_eq_true_eq]
                  simp only [isEvenSignificand, hm_bridge,
                    show 2 ^ (FloatFormat.prec.toNat - 1) % 2 = 0 from by
                      rw [Nat.pow_mod]; simp [show FloatFormat.prec.toNat - 1 ≠ 0 from by
                        have := FloatFormat.valid_prec; omega],
                    decide_true, ↓reduceIte, Fp.neg_finite]
                  simp [FiniteFp.neg_def]
              · -- NearestTiesAwayFromZero (carry, sign=true, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                simp only [hm_bridge.symm]
                rw [neg_mul, rnAway_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_carry]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul]
                  rw [hm_bridge,
                      show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                        from by omega]
                  push_cast
                  rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                        exact_mod_cast (show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega),
                      ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                      ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                      two_zpow_mul, two_zpow_mul]
                  congr 1
                  rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                        have := FloatFormat.valid_prec; omega)]
                  omega)]
                have hge_half : r ≥ half := by
                  revert hru_val; simp [decide_eq_true_eq, Nat.not_lt]
                by_cases hr_gt : r > half
                · rw [if_pos (hr_gt_mid hr_gt), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
                · have hr_eq : r = half := by omega
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
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
            cases sign
            · -- sign = false
              simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · simp at hru_val  -- Down: impossible
              · exact hroundUp_eq.symm  -- Up
              · simp at hru_val  -- TowardZero: impossible (positive val, roundUp ≠ roundTowardZero)
              · -- NearestTiesToEven (no-carry, sign=false, shouldRoundUp=true)
                -- hru_val uses 2^(shift_nat-1), rewrite to use half
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                rw [rnEven_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                by_cases hr_gt : r > half
                · rw [if_neg (not_lt.mpr (le_of_lt (hr_gt_mid hr_gt))),
                      if_pos (hr_gt_mid hr_gt)]
                · -- r ≤ half, shouldRoundUp=true → r = half ∧ q odd
                  have hr_eq : r = half := by
                    by_contra h_ne; have hlt : r < half := by omega
                    simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_val
                    exact absurd hru_val (by decide)
                  rw [if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge),
                      if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le)]
                  have hq_odd : q % 2 ≠ 0 := by
                    simp only [show ¬(r > half) from hr_gt, ite_false,
                      show ¬(r < half) from by omega, ite_false] at hru_val
                    revert hru_val; simp [decide_eq_true_eq]
                  rw [hpred_even, show decide (q % 2 = 0) = false from by simp [hq_odd]]; simp
              · -- NearestTiesAwayFromZero (no-carry, sign=false, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                rw [rnAway_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                -- hru_val : decide (half ≤ r) = true → r ≥ half
                have hge_half : r ≥ half := by
                  revert hru_val; simp [decide_eq_true_eq, Nat.not_lt]
                by_cases hr_gt : r > half
                · rw [if_neg (not_lt.mpr (le_of_lt (hr_gt_mid hr_gt))),
                      if_pos (hr_gt_mid hr_gt)]
                · have hr_eq : r = half := by omega
                  rw [if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge),
                      if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_pos hval_pos]
            · -- sign = true
              simp only [intSigVal, Bool.true_eq_false, ↓reduceIte]
              unfold shouldRoundUp at hru_val
              simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
              have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
              cases mode <;>
                simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
              · -- Down
                rw [neg_mul, roundDown_neg_eq_neg_roundUp _ hval_ne,
                    hroundUp_eq, Fp.neg_finite]; simp [FiniteFp.neg_def]
              · simp at hru_val  -- Up: impossible
              · simp at hru_val  -- TowardZero: impossible
              · -- NearestTiesToEven (no-carry, sign=true, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                rw [neg_mul, rnEven_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                by_cases hr_gt : r > half
                · -- val > mid → -(Fp.finite succ_fp) = Fp.finite ⟨true,...,q+1,...⟩
                  rw [if_pos (hr_gt_mid hr_gt), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
                · have hr_eq : r = half := by
                    by_contra h_ne; have hlt : r < half := by omega
                    simp only [show ¬(r > half) from hr_gt, ite_false, hlt, ite_true] at hru_val
                    exact absurd hru_val (by decide)
                  -- val = mid, isEvenSignificand succ_fp check
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge)]
                  -- q odd → q+1 even → isEvenSignificand succ_fp = true → -(Fp.finite succ_fp)
                  have hq_odd : q % 2 ≠ 0 := by
                    simp only [show ¬(r > half) from hr_gt, ite_false,
                      show ¬(r < half) from by omega, ite_false] at hru_val
                    revert hru_val; simp [decide_eq_true_eq]
                  -- isEvenSignificand checks m % 2 = 0. succ_fp.m = q+1, q odd → q+1 even.
                  simp only [isEvenSignificand, show (q + 1) % 2 = 0 from by omega,
                    decide_true, ↓reduceIte, Fp.neg_finite]
                  simp [FiniteFp.neg_def]
              · -- NearestTiesAwayFromZero (no-carry, sign=true, shouldRoundUp=true)
                rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
                rw [neg_mul, rnAway_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                have hge_half : r ≥ half := by
                  revert hru_val; simp [decide_eq_true_eq, Nat.not_lt]
                by_cases hr_gt : r > half
                · rw [if_pos (hr_gt_mid hr_gt), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
                · have hr_eq : r = half := by omega
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                      if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge), Fp.neg_finite]
                  simp [FiniteFp.neg_def]
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
          -- Dispatch by sign × mode.
          cases sign
          · -- sign = false
            simp only [intSigVal, Bool.false_eq_true, ↓reduceIte]
            -- Goal: Fp.finite ⟨false, ..., q, _⟩ = mode.round(mag * 2^e_base)
            -- First eliminate impossible modes
            unfold shouldRoundUp at hru_val
            simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
            cases mode <;>
              simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
            · exact hroundDown_eq.symm  -- Down
            · simp at hru_val  -- Up: impossible
            · rw [roundTowardZero_pos_eq _ hval_pos]; exact hroundDown_eq.symm  -- TowardZero
            · -- NearestTiesToEven (shouldRoundUp=false, sign=false)
              rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
              by_cases hr_lt : r < half
              · -- r < half: val < midpoint → returns pred
                by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
                · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                    hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                    he_stored_le_inner hq1 h_e_ulp_eq
                  have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
                  rw [rnEven_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                      hroundDown_eq hroundUp_eq]
                  dsimp only
                  rw [hmid_unfold _ (by
                    simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                      Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                    congr 1; ring_nf)]
                  rw [if_pos (hr_lt_mid hr_lt)]
                · -- carry + r < half (TiesToEven, sign=false)
                  push_neg at hq1
                  have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
                  by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
                  · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                      hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                      he_carry hq_eq h_e_ulp_eq
                    have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                    have hm_bridge : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
                      rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
                    rw [rnEven_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                        hroundDown_eq hroundUp_carry]
                    dsimp only
                    rw [hmid_unfold _ (by
                      simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                        Bool.false_eq_true, ↓reduceIte, one_mul]
                      rw [hm_bridge,
                          show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                            from by omega]
                      push_cast
                      rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                            exact_mod_cast hq_eq,
                          ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                          ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                          two_zpow_mul, two_zpow_mul]
                      congr 1
                      rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                            have := FloatFormat.valid_prec; omega)]
                      omega)]
                    rw [if_pos (hr_lt_mid hr_lt)]
                  · push_neg at he_carry
                    have h2ne : (2 : R) ≠ 0 := by norm_num
                    have hpred_is_lff : pred_fp = FiniteFp.largestFiniteFloat := by
                      rw [hpred_fp_def]; ext <;> simp [FiniteFp.largestFiniteFloat,
                        show e_ulp + FloatFormat.prec - 1 = FloatFormat.max_exp from by omega,
                        show q = 2 ^ FloatFormat.prec.toNat - 1 from by omega]
                    have hval_gt_lff : (mag : R) * (2 : R) ^ e_base >
                        FiniteFp.largestFiniteFloat.toVal := by
                      rw [← hpred_is_lff, hpred_toVal, hval_decomp]
                      linarith [mul_pos (Nat.cast_pos.mpr hr_pos)
                        (zpow_pos (show (0:R) < 2 from by norm_num) e_base)]
                    have hroundUp_inf := roundUp_gt_largestFiniteFloat _ hval_pos hval_gt_lff
                    -- zpow building blocks for mid_val = threshold
                    have h_zpow1 : (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ e_ulp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
                      congr 1; rw [FloatFormat.prec_toNat_eq]; omega
                    have h_zpow2 : (2 : R) ^ e_ulp = 2 * (2 : R) ^ (e_ulp - 1) := by
                      rw [show e_ulp = e_ulp - 1 + 1 from by omega, zpow_add₀ h2ne, zpow_one]
                      ring
                    have h_zpow3 : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) *
                        (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ e_ulp := by
                      rw [two_zpow_mul]; congr 1; omega
                    have h_zpow4 : 2 * (2 : R) ^ FloatFormat.max_exp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      rw [zpow_add₀ h2ne, zpow_one]; ring
                    have h_prod : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      have hq1 : (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat := by
                        exact_mod_cast show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega
                      have : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                          ((q : R) + 1) * (2 : R) ^ e_ulp := by ring
                      rw [this, hq1, h_zpow1]
                    have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                        (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp := by
                      suffices hmid_le : mid_val ≤ (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp from
                        lt_of_lt_of_le (hr_lt_mid hr_lt) hmid_le
                      suffices hmid_eq : mid_val = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp from le_of_eq hmid_eq
                      calc mid_val
                          = (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) := hmid_val_def
                        _ = (2 : R) ^ (FloatFormat.max_exp + 1) - (2 : R) ^ (e_ulp - 1) := by
                            linarith [h_prod, h_zpow2]
                        _ = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                            (2 : R) ^ FloatFormat.max_exp := by
                            rw [sub_mul, div_mul_eq_mul_div, h_zpow3, h_zpow2,
                                mul_div_cancel_left₀ _ h2ne, h_zpow4]
                    exact (rnEven_pos_succ_overflow _ pred_fp hval_pos hval_ge_ssps
                      hval_lt_thresh hroundDown_eq hroundUp_inf).symm
              · -- r ≥ half: r = half ∧ q even → at midpoint, pred is even → returns pred
                have hr_not_gt : ¬(r > half) := by
                  intro h; rw [if_pos h] at hru_val; exact absurd hru_val (by decide)
                have hr_eq : r = half := by omega
                have hq_even : q % 2 = 0 := by
                  simp only [hr_not_gt, ite_false, show ¬(r < half) from hr_lt, ite_false] at hru_val
                  revert hru_val; simp [decide_eq_false_iff_not, not_not]
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
                rw [rnEven_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                rw [if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge),
                    if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le)]
                rw [hpred_even, show decide (q % 2 = 0) = true from by simp [hq_even]]
                exact Eq.symm (if_pos rfl)
            · -- NearestTiesAwayFromZero (shouldRoundUp=false, sign=false)
              rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
              have hr_lt : r < half := by
                revert hru_val; simp [decide_eq_false_iff_not, Nat.not_le]
              by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
              · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                  hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                  he_stored_le_inner hq1 h_e_ulp_eq
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
                rw [rnAway_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                rw [if_pos (hr_lt_mid hr_lt)]
              · -- carry + r < half (TiesAwayFromZero, sign=false)
                push_neg at hq1
                have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
                by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
                · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                    hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                    he_carry hq_eq h_e_ulp_eq
                  have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                  have hm_bridge : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
                    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
                  rw [rnAway_pos_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                      hroundDown_eq hroundUp_carry]
                  dsimp only
                  rw [hmid_unfold _ (by
                    simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                      Bool.false_eq_true, ↓reduceIte, one_mul]
                    rw [hm_bridge,
                        show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                          from by omega]
                    push_cast
                    rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                          exact_mod_cast hq_eq,
                        ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                        ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                        two_zpow_mul, two_zpow_mul]
                    congr 1
                    rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                          have := FloatFormat.valid_prec; omega)]
                    omega)]
                  rw [if_pos (hr_lt_mid hr_lt)]
                · push_neg at he_carry
                  have h2ne : (2 : R) ≠ 0 := by norm_num
                  have hpred_is_lff : pred_fp = FiniteFp.largestFiniteFloat := by
                    rw [hpred_fp_def]; ext <;> simp [FiniteFp.largestFiniteFloat,
                      show e_ulp + FloatFormat.prec - 1 = FloatFormat.max_exp from by omega,
                      show q = 2 ^ FloatFormat.prec.toNat - 1 from by omega]
                  have hval_gt_lff : (mag : R) * (2 : R) ^ e_base >
                      FiniteFp.largestFiniteFloat.toVal := by
                    rw [← hpred_is_lff, hpred_toVal, hval_decomp]
                    linarith [mul_pos (Nat.cast_pos.mpr hr_pos)
                      (zpow_pos (show (0:R) < 2 from by norm_num) e_base)]
                  have hroundUp_inf := roundUp_gt_largestFiniteFloat _ hval_pos hval_gt_lff
                  have h_zpow1 : (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ e_ulp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
                    congr 1; rw [FloatFormat.prec_toNat_eq]; omega
                  have h_zpow2 : (2 : R) ^ e_ulp = 2 * (2 : R) ^ (e_ulp - 1) := by
                    rw [show e_ulp = e_ulp - 1 + 1 from by omega, zpow_add₀ h2ne, zpow_one]
                    ring
                  have h_zpow3 : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) *
                      (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ e_ulp := by
                    rw [two_zpow_mul]; congr 1; omega
                  have h_zpow4 : 2 * (2 : R) ^ FloatFormat.max_exp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    rw [zpow_add₀ h2ne, zpow_one]; ring
                  have h_prod : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    have hq1r : (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat := by
                      exact_mod_cast show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega
                    have : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                        ((q : R) + 1) * (2 : R) ^ e_ulp := by ring
                    rw [this, hq1r, h_zpow1]
                  have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                      (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                      (2 : R) ^ FloatFormat.max_exp := by
                    suffices hmid_le : mid_val ≤ (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp from
                      lt_of_lt_of_le (hr_lt_mid hr_lt) hmid_le
                    suffices hmid_eq : mid_val = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp from le_of_eq hmid_eq
                    calc mid_val
                        = (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) := hmid_val_def
                      _ = (2 : R) ^ (FloatFormat.max_exp + 1) - (2 : R) ^ (e_ulp - 1) := by
                          linarith [h_prod, h_zpow2]
                      _ = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp := by
                          rw [sub_mul, div_mul_eq_mul_div, h_zpow3, h_zpow2,
                              mul_div_cancel_left₀ _ h2ne, h_zpow4]
                  exact (rnAway_pos_succ_overflow _ pred_fp hval_pos hval_ge_ssps
                    hval_lt_thresh hroundDown_eq hroundUp_inf).symm
          · -- sign = true
            simp only [intSigVal, Bool.true_eq_false, ↓reduceIte]
            -- Goal: Fp.finite ⟨true, ..., q, _⟩ = mode.round(-(mag * 2^e_base))
            unfold shouldRoundUp at hru_val
            simp only [show r ≠ 0 from by omega, ↓reduceIte] at hru_val
            cases mode <;>
              simp only [RoundingMode.round, RoundingMode.toRoundingFunction] at hru_val ⊢
            · simp at hru_val  -- Down: impossible
            · -- Up: goal is ⟨true,...,q,_⟩ = roundUp(-(mag * 2^e_base))
              -- roundUp(-val) = -(roundDown(val))
              rw [neg_mul, roundUp_neg_eq_neg_roundDown _ hval_ne,
                  hroundDown_eq, Fp.neg_finite]; simp [FiniteFp.neg_def, hpred_fp_def]
            · -- TowardZero
              have hneg_val : -(↑mag : R) * (2:R) ^ e_base < 0 := by
                rw [neg_mul]; exact neg_neg_of_pos hval_pos
              rw [roundTowardZero_neg_eq _ hneg_val,
                  neg_mul, roundUp_neg_eq_neg_roundDown _ hval_ne,
                  hroundDown_eq, Fp.neg_finite]; simp [FiniteFp.neg_def, hpred_fp_def]
            · -- NearestTiesToEven (shouldRoundUp=false, sign=true)
              rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
              by_cases hr_lt : r < half
              · -- r < half
                by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
                · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                    hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                    he_stored_le_inner hq1 h_e_ulp_eq
                  have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
                  rw [neg_mul, rnEven_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                      hroundDown_eq hroundUp_eq]
                  dsimp only
                  rw [hmid_unfold _ (by
                    simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                      Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                    congr 1; ring_nf)]
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (le_of_lt (hr_lt_mid hr_lt))),
                      if_pos (hr_lt_mid hr_lt), Fp.neg_finite]
                  simp [FiniteFp.neg_def, hpred_fp_def]
                · -- carry + r < half (TiesToEven, sign=true)
                  push_neg at hq1
                  have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
                  by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
                  · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                      hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                      he_carry hq_eq h_e_ulp_eq
                    have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                    have hm_bridge : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
                      rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
                    rw [neg_mul, rnEven_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                        hroundDown_eq hroundUp_carry]
                    dsimp only
                    rw [hmid_unfold _ (by
                      simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                        Bool.false_eq_true, ↓reduceIte, one_mul]
                      rw [hm_bridge,
                          show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                            from by omega]
                      push_cast
                      rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                            exact_mod_cast hq_eq,
                          ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                          ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                          two_zpow_mul, two_zpow_mul]
                      congr 1
                      rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                            have := FloatFormat.valid_prec; omega)]
                      omega)]
                    rw [if_neg (show ¬(_ > _) from not_lt.mpr (le_of_lt (hr_lt_mid hr_lt))),
                        if_pos (hr_lt_mid hr_lt), Fp.neg_finite]
                    simp [FiniteFp.neg_def, hpred_fp_def]
                  · push_neg at he_carry
                    have h2ne : (2 : R) ≠ 0 := by norm_num
                    have hpred_is_lff : pred_fp = FiniteFp.largestFiniteFloat := by
                      rw [hpred_fp_def]; ext <;> simp [FiniteFp.largestFiniteFloat,
                        show e_ulp + FloatFormat.prec - 1 = FloatFormat.max_exp from by omega,
                        show q = 2 ^ FloatFormat.prec.toNat - 1 from by omega]
                    have hval_gt_lff : (mag : R) * (2 : R) ^ e_base >
                        FiniteFp.largestFiniteFloat.toVal := by
                      rw [← hpred_is_lff, hpred_toVal, hval_decomp]
                      linarith [mul_pos (Nat.cast_pos.mpr hr_pos)
                        (zpow_pos (show (0:R) < 2 from by norm_num) e_base)]
                    have hroundUp_inf := roundUp_gt_largestFiniteFloat _ hval_pos hval_gt_lff
                    have h_zpow1 : (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ e_ulp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
                      congr 1; rw [FloatFormat.prec_toNat_eq]; omega
                    have h_zpow2 : (2 : R) ^ e_ulp = 2 * (2 : R) ^ (e_ulp - 1) := by
                      rw [show e_ulp = e_ulp - 1 + 1 from by omega, zpow_add₀ h2ne, zpow_one]
                      ring
                    have h_zpow3 : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) *
                        (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ e_ulp := by
                      rw [two_zpow_mul]; congr 1; omega
                    have h_zpow4 : 2 * (2 : R) ^ FloatFormat.max_exp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      rw [zpow_add₀ h2ne, zpow_one]; ring
                    have h_prod : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                        (2 : R) ^ (FloatFormat.max_exp + 1) := by
                      have hq1r : (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat := by
                        exact_mod_cast show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega
                      have : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                          ((q : R) + 1) * (2 : R) ^ e_ulp := by ring
                      rw [this, hq1r, h_zpow1]
                    have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                        (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp := by
                      suffices hmid_le : mid_val ≤ (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp from
                        lt_of_lt_of_le (hr_lt_mid hr_lt) hmid_le
                      suffices hmid_eq : mid_val = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp from le_of_eq hmid_eq
                      calc mid_val
                          = (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) := hmid_val_def
                        _ = (2 : R) ^ (FloatFormat.max_exp + 1) - (2 : R) ^ (e_ulp - 1) := by
                            linarith [h_prod, h_zpow2]
                        _ = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                            (2 : R) ^ FloatFormat.max_exp := by
                            rw [sub_mul, div_mul_eq_mul_div, h_zpow3, h_zpow2,
                                mul_div_cancel_left₀ _ h2ne, h_zpow4]
                    rw [neg_mul, (rnEven_neg_succ_overflow _ pred_fp hval_pos hval_ge_ssps
                        hval_lt_thresh hroundDown_eq hroundUp_inf)]
                    simp [FiniteFp.neg_def, hpred_fp_def]
              · -- r = half ∧ q even
                have hr_not_gt : ¬(r > half) := by
                  intro h; rw [if_pos h] at hru_val; exact absurd hru_val (by decide)
                have hr_eq : r = half := by omega
                have hq_even : q % 2 = 0 := by
                  simp only [hr_not_gt, ite_false, show ¬(r < half) from hr_lt, ite_false] at hru_val
                  revert hru_val; simp [decide_eq_false_iff_not, not_not]
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
                rw [neg_mul, rnEven_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                -- At midpoint, neg unfold checks isEvenSignificand succ_fp
                -- q even → q+1 odd → isEvenSignificand = false → returns -(pred)
                rw [if_neg (show ¬(_ > _) from not_lt.mpr (hr_eq_mid hr_eq).le),
                    if_neg (not_lt.mpr (hr_eq_mid hr_eq).ge)]
                simp only [isEvenSignificand, show (q + 1) % 2 = 1 from by omega,
                  ↓reduceIte, Fp.neg_finite]
                simp [FiniteFp.neg_def, hpred_fp_def]
            · -- NearestTiesAwayFromZero (shouldRoundUp=false, sign=true)
              rw [show 2 ^ (shift_nat - 1) = half from rfl] at hru_val
              have hr_lt : r < half := by
                revert hru_val; simp [decide_eq_false_iff_not, Nat.not_le]
              by_cases hq1 : q + 1 < 2 ^ FloatFormat.prec.toNat
              · have hroundUp_eq := roundUp_nat_mul_zpow (R := R) mag e_base e_ulp q
                  hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                  he_stored_le_inner hq1 h_e_ulp_eq
                have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_eq
                rw [neg_mul, rnAway_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                    hroundDown_eq hroundUp_eq]
                dsimp only
                rw [hmid_unfold _ (by
                  simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                    Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_add, Nat.cast_one]
                  congr 1; ring_nf)]
                rw [if_neg (show ¬(_ > _) from not_lt.mpr (le_of_lt (hr_lt_mid hr_lt))),
                    if_pos (hr_lt_mid hr_lt), Fp.neg_finite]
                simp [FiniteFp.neg_def, hpred_fp_def]
              · -- carry + r < half (TiesAwayFromZero, sign=true)
                push_neg at hq1
                have hq_eq : q + 1 = 2 ^ FloatFormat.prec.toNat := by omega
                by_cases he_carry : e_ulp + FloatFormat.prec ≤ FloatFormat.max_exp
                · have hroundUp_carry := roundUp_nat_mul_zpow_carry (R := R) mag e_base e_ulp q
                    hmag hval_pos hval_lt_overflow hceil_bridge hint_log (by omega)
                    he_carry hq_eq h_e_ulp_eq
                  have hval_lt_thresh := val_lt_thresh_of_roundUp_finite _ _ hval_pos hroundUp_carry
                  have hm_bridge : 2 ^ (FloatFormat.prec - 1).toNat = 2 ^ (FloatFormat.prec.toNat - 1) := by
                    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
                  rw [neg_mul, rnAway_neg_unfold _ pred_fp _ hval_pos hval_ge_ssps hval_lt_thresh
                      hroundDown_eq hroundUp_carry]
                  dsimp only
                  rw [hmid_unfold _ (by
                    simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two,
                      Bool.false_eq_true, ↓reduceIte, one_mul]
                    rw [hm_bridge,
                        show e_ulp + FloatFormat.prec - FloatFormat.prec + 1 = e_ulp + 1
                          from by omega]
                    push_cast
                    rw [show (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat from by
                          exact_mod_cast hq_eq,
                        ← zpow_natCast (2 : R) (FloatFormat.prec.toNat - 1),
                        ← zpow_natCast (2 : R) FloatFormat.prec.toNat,
                        two_zpow_mul, two_zpow_mul]
                    congr 1
                    rw [Nat.cast_sub (show 1 ≤ FloatFormat.prec.toNat from by
                          have := FloatFormat.valid_prec; omega)]
                    omega)]
                  rw [if_neg (show ¬(_ > _) from not_lt.mpr (le_of_lt (hr_lt_mid hr_lt))),
                      if_pos (hr_lt_mid hr_lt), Fp.neg_finite]
                  simp [FiniteFp.neg_def, hpred_fp_def]
                · push_neg at he_carry
                  have h2ne : (2 : R) ≠ 0 := by norm_num
                  have hpred_is_lff : pred_fp = FiniteFp.largestFiniteFloat := by
                    rw [hpred_fp_def]; ext <;> simp [FiniteFp.largestFiniteFloat,
                      show e_ulp + FloatFormat.prec - 1 = FloatFormat.max_exp from by omega,
                      show q = 2 ^ FloatFormat.prec.toNat - 1 from by omega]
                  have hval_gt_lff : (mag : R) * (2 : R) ^ e_base >
                      FiniteFp.largestFiniteFloat.toVal := by
                    rw [← hpred_is_lff, hpred_toVal, hval_decomp]
                    linarith [mul_pos (Nat.cast_pos.mpr hr_pos)
                      (zpow_pos (show (0:R) < 2 from by norm_num) e_base)]
                  have hroundUp_inf := roundUp_gt_largestFiniteFloat _ hval_pos hval_gt_lff
                  have h_zpow1 : (2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ e_ulp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    rw [← zpow_natCast (2 : R) FloatFormat.prec.toNat, two_zpow_mul]
                    congr 1; rw [FloatFormat.prec_toNat_eq]; omega
                  have h_zpow2 : (2 : R) ^ e_ulp = 2 * (2 : R) ^ (e_ulp - 1) := by
                    rw [show e_ulp = e_ulp - 1 + 1 from by omega, zpow_add₀ h2ne, zpow_one]
                    ring
                  have h_zpow3 : (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) *
                      (2 : R) ^ FloatFormat.max_exp = (2 : R) ^ e_ulp := by
                    rw [two_zpow_mul]; congr 1; omega
                  have h_zpow4 : 2 * (2 : R) ^ FloatFormat.max_exp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    rw [zpow_add₀ h2ne, zpow_one]; ring
                  have h_prod : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                      (2 : R) ^ (FloatFormat.max_exp + 1) := by
                    have hq1r : (q : R) + 1 = (2 : R) ^ FloatFormat.prec.toNat := by
                      exact_mod_cast show q + 1 = 2 ^ FloatFormat.prec.toNat from by omega
                    have : (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ e_ulp =
                        ((q : R) + 1) * (2 : R) ^ e_ulp := by ring
                    rw [this, hq1r, h_zpow1]
                  have hval_lt_thresh : (mag : R) * (2 : R) ^ e_base <
                      (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                      (2 : R) ^ FloatFormat.max_exp := by
                    suffices hmid_le : mid_val ≤ (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp from
                      lt_of_lt_of_le (hr_lt_mid hr_lt) hmid_le
                    suffices hmid_eq : mid_val = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                        (2 : R) ^ FloatFormat.max_exp from le_of_eq hmid_eq
                    calc mid_val
                        = (q : R) * (2 : R) ^ e_ulp + (2 : R) ^ (e_ulp - 1) := hmid_val_def
                      _ = (2 : R) ^ (FloatFormat.max_exp + 1) - (2 : R) ^ (e_ulp - 1) := by
                          linarith [h_prod, h_zpow2]
                      _ = (2 - (2 : R) ^ (1 - (FloatFormat.prec : ℤ)) / 2) *
                          (2 : R) ^ FloatFormat.max_exp := by
                          rw [sub_mul, div_mul_eq_mul_div, h_zpow3, h_zpow2,
                              mul_div_cancel_left₀ _ h2ne, h_zpow4]
                  rw [neg_mul, (rnAway_neg_succ_overflow _ pred_fp hval_pos hval_ge_ssps
                      hval_lt_thresh hroundDown_eq hroundUp_inf)]
                  simp [FiniteFp.neg_def, hpred_fp_def]

end roundIntSig_correctness

/-! ## fpAddFinite Correctness -/

/-- For nonzero sums, `fpAddFinite` correctly rounds the exact sum.

Note: the `hsum ≠ 0` condition excludes the signed-zero case where IEEE 754 prescribes
special behavior (returning -0 in Down mode) that differs from `mode.round 0 = +0`. -/
theorem fpAddFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp)
    (hsum : (a.toVal : R) + b.toVal ≠ 0) :
    fpAddFinite mode a b = mode.round ((a.toVal : R) + b.toVal) := by
  -- First get the exact sum representation
  have hexact := fpAddFinite_exact_sum R a b
  -- Name the integer sum
  set e_min := min a.e b.e with e_min_def
  set isum : ℤ := (if a.s = true then -(a.m : ℤ) else ↑a.m) * 2 ^ (a.e - e_min).toNat +
    (if b.s = true then -(b.m : ℤ) else ↑b.m) * 2 ^ (b.e - e_min).toNat with isum_def
  -- The integer sum is nonzero
  have hsum_ne : isum ≠ 0 := by
    intro hzero
    apply hsum; rw [hexact, hzero, Int.cast_zero, zero_mul]
  -- Unfold fpAddFinite
  simp only [fpAddFinite, isum_def.symm, e_min_def.symm]
  rw [if_neg hsum_ne]
  -- Now apply roundIntSig_correct
  have hmag_ne : isum.natAbs ≠ 0 := by rwa [Int.natAbs_ne_zero]
  -- val ≥ ssps: |isum| ≥ 1 and e_base = e_min - prec + 1 ≥ min_exp - prec + 1
  have hval_ge_ssps : (isum.natAbs : R) * (2 : R) ^ (e_min - FloatFormat.prec + 1) ≥
      FiniteFp.smallestPosSubnormal.toVal := by
    have hmag_pos : (1 : R) ≤ (isum.natAbs : R) := by
      rw [← Nat.cast_one]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmag_ne
    have he_base_ge : e_min - FloatFormat.prec + 1 ≥ FloatFormat.min_exp - FloatFormat.prec + 1 := by
      have ha_ge := a.valid.1  -- a.e ≥ min_exp
      have hb_ge := b.valid.1  -- b.e ≥ min_exp
      omega
    rw [ge_iff_le, FiniteFp.smallestPosSubnormal_toVal]
    calc (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
      _ ≤ (2 : R) ^ (e_min - FloatFormat.prec + 1) :=
          zpow_le_zpow_right₀ (by norm_num) he_base_ge
      _ = 1 * (2 : R) ^ (e_min - FloatFormat.prec + 1) := by ring
      _ ≤ (isum.natAbs : R) * (2 : R) ^ (e_min - FloatFormat.prec + 1) :=
          mul_le_mul_of_nonneg_right hmag_pos (by positivity)
  rw [roundIntSig_correct (R := R) mode _ _ _ hmag_ne hval_ge_ssps]
  -- Show the arguments to mode.round are equal
  congr 1
  rw [intSigVal_eq_int_mul (R := R) hsum_ne, hexact]

end Add
