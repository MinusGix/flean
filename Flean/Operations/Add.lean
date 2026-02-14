import Flean.Operations.RoundIntSig

/-! # Floating-Point Addition

Softfloat-style floating-point addition using `roundIntSigM` as the rounding primitive.

The algorithm for adding two finite floats:
1. Align exponents to a common base
2. Compute the signed integer sum of the aligned significands
3. Handle the zero-sum case (IEEE 754 signed zero rules)
4. For nonzero sums, delegate to `roundIntSigM`
-/

section Add

variable [FloatFormat]
local notation "prec" => FloatFormat.prec

/-- Add two finite floating-point numbers with contextual rounding policy.

The exact sum `a.toVal + b.toVal` equals `sum × 2^(e_min - prec + 1)` where
`sum` is the signed integer sum of aligned significands. That exact integer
representation is then rounded via `roundIntSigM`. -/
def fpAddFinite [RModeExec] (a b : FiniteFp) : Fp :=
  let e_min := min a.e b.e
  -- Align significands to common exponent e_min - prec + 1.
  let sa : ℤ := condNeg a.s (a.m : ℤ) * 2^(a.e - e_min).toNat
  let sb : ℤ := condNeg b.s (b.m : ℤ) * 2^(b.e - e_min).toNat
  let sum := sa + sb
  if sum = 0 then
    -- IEEE 754 exact-cancellation signed-zero rule.
    let result_sign : Bool := exactCancelSign a.s b.s
    Fp.finite ⟨result_sign, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  else
    let sign := decide (sum < 0)
    let mag := sum.natAbs
    roundIntSigM sign mag (e_min - prec + 1)

instance [RModeExec] : HAdd FiniteFp FiniteFp Fp where
  hAdd := fpAddFinite

@[simp] theorem add_finite_eq_fpAddFinite [RModeExec] (x y : FiniteFp) : x + y = fpAddFinite x y := rfl

/-- IEEE 754 floating-point addition with full special-case handling.

Special cases:
- Any NaN operand produces NaN
- `∞ + ∞` (same sign) = `∞`
- `∞ + (-∞)` = NaN
- `∞ + finite` = `∞`
- `finite + finite` delegates to `fpAddFinite` -/
def fpAdd [RModeExec] (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | .infinite sx, .infinite sy =>
    if sx = sy then .infinite sx
    else .NaN
  | .infinite s, .finite _ => .infinite s
  | .finite _, .infinite s => .infinite s
  | .finite a, .finite b => a + b

instance [RModeExec] : HAdd Fp Fp Fp where
  hAdd := fpAdd

@[simp] theorem add_eq_fpAdd [RModeExec] (x y : Fp) : x + y = fpAdd x y := rfl

/-! ## Commutativity -/

/-- The exact-cancellation signed-zero sign is symmetric in operand order. -/
private theorem exact_cancel_sign_comm [RModeExec] (as bs : Bool) :
    exactCancelSign as bs = exactCancelSign bs as := by
  cases as <;> cases bs <;> simp [exactCancelSign]

/-- `fpAddFinite` is commutative. -/
theorem fpAddFinite_comm [RModeExec] (a b : FiniteFp) :
    fpAddFinite a b = fpAddFinite b a := by
  simp only [fpAddFinite, min_comm a.e b.e, add_comm
    (condNeg a.s (a.m : ℤ) * 2 ^ (a.e - min b.e a.e).toNat)
    (condNeg b.s (b.m : ℤ) * 2 ^ (b.e - min b.e a.e).toNat),
    exact_cancel_sign_comm a.s b.s, eq_comm]

/-- `fpAdd` is commutative. -/
theorem fpAdd_comm [RModeExec] (x y : Fp) :
    x + y = y + x := by
  cases x with
  | NaN => cases y <;> simp [add_eq_fpAdd, fpAdd]
  | infinite sx =>
    cases y with
    | NaN => simp [add_eq_fpAdd, fpAdd]
    | infinite sy =>
      simp only [add_eq_fpAdd, fpAdd]
      by_cases h : sx = sy
      · simp [h]
      · have h' : ¬(sy = sx) := fun h' => h (h'.symm)
        simp [h, h']
    | finite b => simp [add_eq_fpAdd, fpAdd]
  | finite a =>
    cases y with
    | NaN => simp [add_eq_fpAdd, fpAdd]
    | infinite sy => simp [add_eq_fpAdd, fpAdd]
    | finite b => simp [add_eq_fpAdd, fpAdd, fpAddFinite_comm]

/-! ## Representation Lemma -/

/-- Signed integer view of a finite float significand. -/
abbrev finiteSignedInt (x : FiniteFp) : ℤ :=
  condNeg x.s (x.m : ℤ)

/-- Align a finite float's signed significand to exponent base `e_min`. -/
abbrev alignedSignedInt (x : FiniteFp) (e_min : ℤ) : ℤ :=
  finiteSignedInt x * 2 ^ (x.e - e_min).toNat

/-- First aligned signed term in finite addition. -/
abbrev addAlignedIntA (a b : FiniteFp) : ℤ :=
  alignedSignedInt a (min a.e b.e)

/-- Second aligned signed term in finite addition. -/
abbrev addAlignedIntB (a b : FiniteFp) : ℤ :=
  alignedSignedInt b (min a.e b.e)

/-- Signed aligned integer sum for finite addition. -/
abbrev addAlignedSumInt (a b : FiniteFp) : ℤ :=
  addAlignedIntA a b + addAlignedIntB a b

/-- Exact-cancellation branch of `fpAddFinite`: result is signed zero with
    sign chosen by `exactCancelSign`. -/
theorem fpAddFinite_exact_cancel_sign [RModeExec] (a b : FiniteFp)
    (hsum : addAlignedSumInt a b = 0) :
    fpAddFinite a b =
      Fp.finite ⟨exactCancelSign a.s b.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩ := by
  simp [fpAddFinite, hsum]

/-- Policy-facing form of `fpAddFinite_exact_cancel_sign`. -/
theorem fpAddFinite_exact_cancel_sign_eq_policy {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RModePolicySpec R]
    (a b : FiniteFp) (hsum : addAlignedSumInt a b = 0) :
    fpAddFinite a b =
      Fp.finite
        ⟨if a.s = b.s then a.s
          else policyCancelSignOnExactZero (RModePolicyTag.kind (R := R)),
          FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩ := by
  rw [fpAddFinite_exact_cancel_sign (a := a) (b := b) hsum]
  simp [exactCancelSign_eq_policy (R := R)]

/-- The signed integer for a single operand, scaled by 2^(e_min - prec + 1), equals toVal.
    For operand `x` with `e_min ≤ x.e`:
    `(if x.s then -x.m else x.m) * 2^(x.e - e_min) * 2^(e_min - prec + 1) = x.toVal` -/
theorem signed_int_mul_zpow_eq_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : FiniteFp) (e_min : ℤ) (he : e_min ≤ x.e) :
    (condNeg x.s (x.m : ℤ) * 2^(x.e - e_min).toNat : ℤ) *
      (2 : R)^(e_min - prec + 1) = (x.toVal : R) := by
  -- Expand toVal
  unfold FiniteFp.toVal FiniteFp.sign'
  rw [FloatFormat.radix_val_eq_two]
  -- Both sides have the form sign * m * 2^exponent
  -- LHS: (±m * 2^(e-e_min)) * 2^(e_min-p+1) cast to R
  -- RHS: (if s then -1 else 1) * m * 2^(e-p+1) in R
  -- Key: 2^(e-e_min) * 2^(e_min-p+1) = 2^(e-p+1) since (e-e_min) + (e_min-p+1) = e-p+1
  push_cast
  unfold condNeg
  -- Now convert ↑(2^(x.e - e_min).toNat) to (2:R)^(x.e - e_min)
  have hnn : 0 ≤ x.e - e_min := by omega
  rw [show (x.e - e_min).toNat = (x.e - e_min).toNat from rfl]
  rw [← zpow_natCast (2 : R) (x.e - e_min).toNat]
  rw [Int.toNat_of_nonneg hnn]
  -- Now combine: 2^(x.e - e_min) * 2^(e_min - prec + 1) = 2^(x.e - prec + 1)
  -- Key: 2^(x.e - e_min) * 2^(e_min - prec + 1) = 2^(x.e - prec + 1)
  have hexp : (2 : R) ^ (x.e - e_min) * (2 : R) ^ (e_min - prec + 1) =
      (2 : R) ^ (x.e - prec + 1) := by
    rw [two_zpow_mul]; congr 1; omega
  split_ifs with hs
  · rw [mul_assoc, hexp]
    simp [hs, mul_assoc, mul_left_comm, mul_comm]
  · rw [mul_assoc, hexp]
    simp [hs, mul_assoc, mul_left_comm, mul_comm]

/-- The integer sum in fpAddFinite exactly represents `a.toVal + b.toVal`.

`(a.toVal : R) + b.toVal =
  addAlignedSumInt a b * (2 : R)^(min a.e b.e - prec + 1)`

where `e_min = min a.e b.e`, `sa` and `sb` are the aligned signed integers. -/
theorem fpAddFinite_exact_sum (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : FiniteFp) :
    (a.toVal : R) + b.toVal =
    ((addAlignedSumInt a b : ℤ) : R) * (2 : R)^(min a.e b.e - prec + 1) := by
  have ha :
      ((addAlignedIntA a b : ℤ) : R) * (2 : R) ^ (min a.e b.e - prec + 1) =
        (a.toVal : R) :=
    signed_int_mul_zpow_eq_toVal a (min a.e b.e) (min_le_left _ _)
  have hb :
      ((addAlignedIntB a b : ℤ) : R) * (2 : R) ^ (min a.e b.e - prec + 1) =
        (b.toVal : R) :=
    signed_int_mul_zpow_eq_toVal b (min a.e b.e) (min_le_right _ _)
  rw [Int.cast_add, add_mul]
  rw [← ha, ← hb]

/-! ## fpAddFinite Correctness -/

/-- Class-driven correctness for nonzero finite sums. -/
theorem fpAddFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp)
    (hsum : (a.toVal : R) + b.toVal ≠ 0) :
    a + b = ○((a.toVal : R) + b.toVal) := by
  have hexact := fpAddFinite_exact_sum R a b
  set e_min := min a.e b.e with e_min_def
  set isum : ℤ := addAlignedSumInt a b with isum_def
  have hsum_ne : isum ≠ 0 := by
    intro hzero
    apply hsum
    rw [hexact, hzero, Int.cast_zero, zero_mul]
  simp only [add_finite_eq_fpAddFinite, fpAddFinite, e_min_def.symm]
  rw [if_neg hsum_ne]
  have hmag_ne : isum.natAbs ≠ 0 := by rwa [Int.natAbs_ne_zero]
  rw [roundIntSigM_correct_tc (R := R) _ _ _ hmag_ne]
  congr 1
  rw [intSigVal_eq_int_mul (R := R) hsum_ne, hexact]

/-- When both positive operands are subnormal and their significands fit in one word,
    rounding their sum under the contextual policy returns their exact sum. -/
theorem subnormal_sum_exact {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RModeIdem R]
    (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (hb_nz : b.m ≠ 0)
    (ha_sub : isSubnormal a.e a.m) (hb_sub : isSubnormal b.e b.m)
    (hfit : a.m + b.m < 2 ^ precNat) :
    ∃ g : FiniteFp, g.s = false ∧
      (g.toVal : R) = (a.toVal : R) + b.toVal ∧
      ○((a.toVal : R) + b.toVal) = Fp.finite g := by
  have hmag_pos : 0 < a.m + b.m := by omega
  obtain ⟨g, hgs, hgv⟩ := exists_finiteFp_of_nat_mul_zpow (R := R) (a.m + b.m)
    (FloatFormat.min_exp - prec + 1) hmag_pos hfit
    (by omega) (by have := FloatFormat.exp_order; omega)
  have hgv_eq : (g.toVal : R) = a.toVal + b.toVal := by
    rw [hgv, FiniteFp.toVal_pos_eq a ha, FiniteFp.toVal_pos_eq b hb, ha_sub.1, hb_sub.1]
    push_cast; ring
  have hround := RModeIdem.round_idempotent (R := R) g (Or.inl hgs)
  rw [hgv_eq] at hround
  exact ⟨g, hgs, hgv_eq, hround⟩

end Add
