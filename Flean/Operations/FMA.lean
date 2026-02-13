import Flean.Operations.Add
import Flean.Operations.Mul

/-! # Floating-Point Fused Multiply-Add (FMA)

Softfloat-style FMA computing `round(a × b + c)` with a single rounding.

The algorithm:
1. Compute the exact product `a.m * b.m` (up to 2p bits)
2. Treat the product as a "virtual float" with stored exponent `a.e + b.e - prec + 1`
3. Align with `c` to a common exponent base (same technique as fpAdd)
4. Compute the signed integer sum of aligned significands
5. Handle the zero-sum case (IEEE 754 signed zero rules)
6. For nonzero sums, delegate to `roundIntSig`

Because the exact product and addend are both rationals with power-of-2 denominators,
their sum is always exactly representable as an integer times a power of 2. This avoids
the need for sticky-bit approximation (unlike division/sqrt).
-/

section FMA

variable [FloatFormat]
local notation "prec" => FloatFormat.prec

/-- Fused multiply-add of three finite floating-point numbers.

The exact value `a.toVal × b.toVal + c.toVal` equals `sum × 2^(e_min - prec + 1)` where
`sum` is the signed integer sum of the aligned product and addend significands. -/
def fpFMAFinite (mode : RoundingMode) (a b c : FiniteFp) : Fp :=
  -- Product as a "virtual float": magnitude a.m * b.m, stored exponent prod_E
  let prod_E := a.e + b.e - prec + 1
  let e_min := min prod_E c.e
  -- Align signed significands to common exponent base e_min - prec + 1
  let sp : ℤ := condNeg (a.s ^^ b.s) ((a.m * b.m : ℕ) : ℤ) *
    2^(prod_E - e_min).toNat
  let sc : ℤ := condNeg c.s (c.m : ℤ) * 2^(c.e - e_min).toNat
  let sum := sp + sc
  if sum = 0 then
    -- IEEE 754 signed zero rules (same as fpAdd):
    -- If product and addend have the same sign, result has that sign
    -- Otherwise, +0 (except in roundDown mode, which gives -0)
    let result_sign : Bool :=
      if (a.s ^^ b.s) = c.s then (a.s ^^ b.s)
      else match mode with
        | .Down => true
        | _ => false
    Fp.finite ⟨result_sign, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  else
    let sign := decide (sum < 0)
    let mag := sum.natAbs
    letI : RModeExec := rModeExecOf mode
    roundIntSigM sign mag (e_min - prec + 1)

/-- IEEE 754 floating-point fused multiply-add with full special-case handling.

Computes `round(x × y + z)` with a single rounding.

Special cases:
- Any NaN operand produces NaN
- ∞ × 0 + z = NaN (indeterminate product, regardless of z)
- 0 × ∞ + z = NaN
- ∞ × ∞ + z: product is ∞, then ∞ + z follows addition rules
- ∞ × finite(nonzero) + z: product is ∞, then ∞ + z follows addition rules
- finite × finite + ∞ = ∞
- finite × finite + finite delegates to `fpFMAFinite` -/
def fpFMA (mode : RoundingMode) (x y z : Fp) : Fp :=
  match x, y, z with
  | .NaN, _, _ | _, .NaN, _ | _, _, .NaN => .NaN
  -- Both multiplicands infinite: product is ∞ with sign x.s ^^ y.s
  | .infinite sx, .infinite sy, .infinite sz =>
    if (sx ^^ sy) = sz then .infinite sz else .NaN
  | .infinite sx, .infinite sy, .finite _ =>
    .infinite (sx ^^ sy)
  -- One multiplicand infinite, one finite
  | .infinite sx, .finite fy, .infinite sz =>
    if fy.m = 0 then .NaN  -- ∞ × 0 = NaN
    else if (sx ^^ fy.s) = sz then .infinite sz else .NaN
  | .infinite sx, .finite fy, .finite _ =>
    if fy.m = 0 then .NaN else .infinite (sx ^^ fy.s)
  | .finite fx, .infinite sy, .infinite sz =>
    if fx.m = 0 then .NaN
    else if (fx.s ^^ sy) = sz then .infinite sz else .NaN
  | .finite fx, .infinite sy, .finite _ =>
    if fx.m = 0 then .NaN else .infinite (fx.s ^^ sy)
  -- Both multiplicands finite, addend infinite: finite + ∞ = ∞
  | .finite _, .finite _, .infinite sz => .infinite sz
  -- All finite
  | .finite a, .finite b, .finite c => fpFMAFinite mode a b c

/-! ## Representation Lemma -/

/-- Stored exponent of the exact product `a * b` as a virtual finite float. -/
abbrev fmaProdE (a b : FiniteFp) : ℤ :=
  a.e + b.e - prec + 1

/-- Common alignment exponent for the fused product-add sum. -/
abbrev fmaEMin (a b c : FiniteFp) : ℤ :=
  min (fmaProdE a b) c.e

/-- Aligned signed integer term contributed by the product `a * b`. -/
abbrev fmaAlignedProdInt (a b c : FiniteFp) : ℤ :=
  condNeg (a.s ^^ b.s) ((a.m * b.m : ℕ) : ℤ) *
    2 ^ (fmaProdE a b - fmaEMin a b c).toNat

/-- Aligned signed integer term contributed by the addend `c`. -/
abbrev fmaAlignedAddInt (a b c : FiniteFp) : ℤ :=
  condNeg c.s (c.m : ℤ) * 2 ^ (c.e - fmaEMin a b c).toNat

/-- Signed aligned integer sum for the exact fused product-add value. -/
abbrev fmaAlignedSumInt (a b c : FiniteFp) : ℤ :=
  fmaAlignedProdInt a b c + fmaAlignedAddInt a b c

/-- The signed product `±(a.m * b.m)`, aligned to exponent `e_min` and scaled by
    `2^(e_min - prec + 1)`, equals `a.toVal * b.toVal`.

    This is the product analogue of `signed_int_mul_zpow_eq_toVal`. -/
theorem signed_product_mul_zpow_eq_product {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (a b : FiniteFp) (e_min : ℤ) (he : e_min ≤ a.e + b.e - prec + 1) :
    (condNeg (a.s ^^ b.s) ((a.m * b.m : ℕ) : ℤ) *
      2^(a.e + b.e - prec + 1 - e_min).toNat : ℤ) *
      (2 : R)^(e_min - prec + 1) = (a.toVal : R) * b.toVal := by
  -- Rewrite product via fpMulFinite_exact_product
  rw [fpMulFinite_exact_product (R := R) a b]
  unfold intSigVal
  push_cast
  unfold condNeg
  have hnn : 0 ≤ a.e + b.e - prec + 1 - e_min := by omega
  rw [← zpow_natCast (2 : R) (a.e + b.e - prec + 1 - e_min).toNat,
      Int.toNat_of_nonneg hnn]
  have hexp : (2 : R) ^ (a.e + b.e - prec + 1 - e_min) *
      (2 : R) ^ (e_min - prec + 1) =
      (2 : R) ^ (a.e + b.e - 2 * prec + 2) := by
    rw [two_zpow_mul]; congr 1; omega
  split_ifs with hs
  · rw [mul_assoc, hexp]
    simp [hs, mul_assoc, mul_left_comm, mul_comm]
  · rw [mul_assoc, hexp]
    simp [hs, mul_assoc, mul_left_comm, mul_comm]

/-- The integer sum in fpFMAFinite exactly represents `a.toVal * b.toVal + c.toVal`.

`(a.toVal : R) * b.toVal + c.toVal =
  fmaAlignedSumInt a b c * (2 : R)^(fmaEMin a b c - prec + 1)`

where `e_min = min (a.e + b.e - prec + 1) c.e`, `sp` is the aligned signed product,
and `sc` is the aligned signed addend. -/
theorem fpFMAFinite_exact_sum (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : FiniteFp) :
    (a.toVal : R) * b.toVal + c.toVal =
    ((fmaAlignedSumInt a b c : ℤ) : R) * (2 : R)^(fmaEMin a b c - prec + 1) := by
  have hprod :
      ((fmaAlignedProdInt a b c : ℤ) : R) * (2 : R) ^ (fmaEMin a b c - prec + 1) =
        (a.toVal : R) * b.toVal :=
    signed_product_mul_zpow_eq_product a b (fmaEMin a b c)
      (by simp [fmaEMin, fmaProdE])
  have hadd :
      ((fmaAlignedAddInt a b c : ℤ) : R) * (2 : R) ^ (fmaEMin a b c - prec + 1) =
        (c.toVal : R) :=
    signed_int_mul_zpow_eq_toVal c (fmaEMin a b c)
      (by simp [fmaEMin, fmaProdE])
  rw [Int.cast_add, add_mul]
  rw [← hprod, ← hadd]

/-! ## fpFMAFinite Correctness -/

/-- For nonzero results, `fpFMAFinite` correctly rounds the exact fused product-sum.

Note: the `hsum ≠ 0` condition excludes the signed-zero case where IEEE 754 prescribes
special behavior that differs from `mode.round 0 = +0`. -/
theorem fpFMAFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R]
    (mode : RoundingMode) (a b c : FiniteFp)
    (hsum : (a.toVal : R) * b.toVal + c.toVal ≠ 0) :
    fpFMAFinite mode a b c = mode.round ((a.toVal : R) * b.toVal + c.toVal) := by
  -- Get the exact sum representation
  have hexact := fpFMAFinite_exact_sum R a b c
  -- Name the aligned integer sum and base exponent
  set e_min := fmaEMin a b c with e_min_def
  set isum : ℤ := fmaAlignedSumInt a b c with isum_def
  -- The integer sum is nonzero
  have hsum_ne : isum ≠ 0 := by
    intro hzero
    apply hsum
    rw [hexact, hzero, Int.cast_zero, zero_mul]
  -- Unfold fpFMAFinite
  simp only [fpFMAFinite, e_min_def.symm]
  rw [if_neg hsum_ne]
  -- Apply generic roundIntSigM correctness
  have hmag_ne : isum.natAbs ≠ 0 := by rwa [Int.natAbs_ne_zero]
  have hround :
      @roundIntSigM _ (rModeExecOf mode) (decide (isum < 0)) isum.natAbs (e_min - prec + 1) =
        mode.round (intSigVal (R := R) (decide (isum < 0)) isum.natAbs (e_min - prec + 1)) := by
    simpa using
      (roundIntSigM_correct (R := R) mode
        (decide (isum < 0)) isum.natAbs (e_min - prec + 1) hmag_ne)
  rw [hround]
  -- Show the arguments to mode.round are equal
  congr 1
  rw [intSigVal_eq_int_mul (R := R) hsum_ne, hexact]

/-! ## Commutativity -/

/-- `fpFMAFinite` is commutative in the first two operands. -/
theorem fpFMAFinite_comm_ab (mode : RoundingMode) (a b c : FiniteFp) :
    fpFMAFinite mode a b c = fpFMAFinite mode b a c := by
  simp only [fpFMAFinite, Bool.xor_comm a.s b.s, Nat.mul_comm a.m b.m, add_comm a.e b.e]

/-- `fpFMA` is commutative in the first two operands. -/
theorem fpFMA_comm_ab (mode : RoundingMode) (x y z : Fp) :
    fpFMA mode x y z = fpFMA mode y x z := by
  cases x with
  | NaN => cases y <;> cases z <;> simp [fpFMA]
  | infinite sx =>
    cases y with
    | NaN => cases z <;> simp [fpFMA]
    | infinite sy => cases z <;> simp [fpFMA, Bool.xor_comm]
    | finite fy =>
      cases z <;> simp only [fpFMA] <;> by_cases hm : fy.m = 0 <;> simp [hm, Bool.xor_comm]
  | finite fx =>
    cases y with
    | NaN => cases z <;> simp [fpFMA]
    | infinite sy =>
      cases z <;> simp only [fpFMA] <;> by_cases hm : fx.m = 0 <;> simp [hm, Bool.xor_comm]
    | finite fy => cases z <;> simp [fpFMA, fpFMAFinite_comm_ab]

/-! ## Negation of both multiplicands -/

/-- Negating both multiplicands in `fpFMAFinite` is a no-op, since `(-a) × (-b) = a × b`. -/
theorem fpFMAFinite_neg_mul_neg (mode : RoundingMode) (a b c : FiniteFp) :
    fpFMAFinite mode (-a) (-b) c = fpFMAFinite mode a b c := by
  simp only [fpFMAFinite, FiniteFp.neg_def, Bool.not_xor_not]

/-- Negating both multiplicands in `fpFMA` is a no-op, since `(-x) × (-y) = x × y`. -/
theorem fpFMA_neg_mul_neg (mode : RoundingMode) (x y z : Fp) :
    fpFMA mode (-x) (-y) z = fpFMA mode x y z := by
  cases x with
  | NaN => cases y <;> cases z <;> simp [fpFMA]
  | infinite sx =>
    cases y with
    | NaN => cases z <;> simp [fpFMA, Fp.neg_def]
    | infinite sy => cases z <;> simp [fpFMA, Fp.neg_def, Bool.not_xor_not]
    | finite fy =>
      cases z <;> simp [fpFMA, Fp.neg_def, Fp.neg_finite, FiniteFp.neg_def, Bool.not_xor_not]
  | finite fx =>
    cases y with
    | NaN => cases z <;> simp [fpFMA, Fp.neg_def]
    | infinite sy =>
      cases z <;> simp [fpFMA, Fp.neg_def, Fp.neg_finite, FiniteFp.neg_def, Bool.not_xor_not]
    | finite fy =>
      cases z <;> simp [fpFMA, fpFMAFinite_neg_mul_neg]

/-! ## Reduction to simpler operations -/

/-- `fpFMAFinite mode a b 0 = fpMulFinite mode a b` when the product is nonzero.

This shows FMA generalizes multiplication: `round(a × b + 0) = round(a × b)`. -/
theorem fpFMAFinite_zero_eq_fpMulFinite {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a b : FiniteFp)
    (hprod : (a.toVal : R) * b.toVal ≠ 0) :
    fpFMAFinite mode a b 0 = fpMulFinite mode a b := by
  have hfma := fpFMAFinite_correct (R := R) mode a b 0
    (by rw [FiniteFp.toVal_zero, add_zero]; exact hprod)
  have hmul := fpMulFinite_correct (R := R) mode a b hprod
  rw [hfma, hmul, FiniteFp.toVal_zero, add_zero]

/-- `fpFMAFinite mode 1 a c = fpAddFinite mode a c` when the sum `a + c` is nonzero.

This shows FMA generalizes addition: `round(1 × a + c) = round(a + c)`. -/
theorem fpFMAFinite_one_eq_fpAddFinite {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (mode : RoundingMode) (a c : FiniteFp)
    (hsum : (a.toVal : R) + c.toVal ≠ 0) :
    fpFMAFinite mode 1 a c = fpAddFinite mode a c := by
  have hfma := fpFMAFinite_correct (R := R) mode 1 a c
    (by rw [FiniteFp.toVal_one, one_mul]; exact hsum)
  have hadd := fpAddFinite_correct (R := R) mode a c hsum
  rw [hfma, hadd, FiniteFp.toVal_one, one_mul]

end FMA
