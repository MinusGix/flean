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
6. For nonzero sums, delegate to `roundIntSigM`

Because the exact product and addend are both rationals with power-of-2 denominators,
their sum is always exactly representable as an integer times a power of 2. This avoids
the need for sticky-bit approximation (unlike division/sqrt).
-/

section FMA

variable [FloatFormat]
local notation "prec" => FloatFormat.prec

/-- Fused multiply-add of finite floats with contextual rounding policy.

Computes `round(a * b + c)` with a single final rounding:
- product and addend are aligned to a common exponent,
- exact integer sum is formed,
- exact-cancellation signed-zero rule is applied,
- nonzero sums are rounded via `roundIntSigM`. -/
def fpFMAFinite [RModeExec] (a b c : FiniteFp) : Fp :=
  let prod_E := a.e + b.e - prec + 1
  let e_min := min prod_E c.e
  let sp : ℤ := condNeg (a.s ^^ b.s) ((a.m * b.m : ℕ) : ℤ) *
    2^(prod_E - e_min).toNat
  let sc : ℤ := condNeg c.s (c.m : ℤ) * 2^(c.e - e_min).toNat
  let sum := sp + sc
  if sum = 0 then
    let result_sign : Bool := exactCancelSign (a.s ^^ b.s) c.s
    Fp.finite ⟨result_sign, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  else
    let sign := decide (sum < 0)
    let mag := sum.natAbs
    roundIntSigM sign mag (e_min - prec + 1)

/-- IEEE 754 fused multiply-add with full special-case handling.

Includes NaN propagation, invalid forms like `∞ * 0`, and infinite-result sign
rules; finite-finite-finite case delegates to `fpFMAFinite`. -/
def fpFMA [RModeExec] (x y z : Fp) : Fp :=
  match x, y, z with
  | .NaN, _, _ | _, .NaN, _ | _, _, .NaN => .NaN
  | .infinite sx, .infinite sy, .infinite sz =>
    if (sx ^^ sy) = sz then .infinite sz else .NaN
  | .infinite sx, .infinite sy, .finite _ =>
    .infinite (sx ^^ sy)
  | .infinite sx, .finite fy, .infinite sz =>
    if fy.m = 0 then .NaN
    else if (sx ^^ fy.s) = sz then .infinite sz else .NaN
  | .infinite sx, .finite fy, .finite _ =>
    if fy.m = 0 then .NaN else .infinite (sx ^^ fy.s)
  | .finite fx, .infinite sy, .infinite sz =>
    if fx.m = 0 then .NaN
    else if (fx.s ^^ sy) = sz then .infinite sz else .NaN
  | .finite fx, .infinite sy, .finite _ =>
    if fx.m = 0 then .NaN else .infinite (fx.s ^^ sy)
  | .finite _, .finite _, .infinite sz => .infinite sz
  | .finite a, .finite b, .finite c => fpFMAFinite a b c

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

/-- Exact-cancellation branch of `fpFMAFinite`: result is signed zero with
    sign chosen by `exactCancelSign` from product-sign and addend-sign. -/
theorem fpFMAFinite_exact_cancel_sign [RModeExec] (a b c : FiniteFp)
    (hsum : fmaAlignedSumInt a b c = 0) :
    fpFMAFinite a b c =
      Fp.finite
        ⟨exactCancelSign (a.s ^^ b.s) c.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩ := by
  have hsum' :
      condNeg (a.s ^^ b.s) (((a.m : ℤ) * (b.m : ℤ))) *
          2 ^ (fmaProdE a b - fmaEMin a b c).toNat +
        condNeg c.s (c.m : ℤ) * 2 ^ (c.e - fmaEMin a b c).toNat = 0 := by
    simpa [fmaAlignedSumInt, fmaAlignedProdInt, fmaAlignedAddInt] using hsum
  simp [fpFMAFinite, hsum']

/-- Policy-facing form of `fpFMAFinite_exact_cancel_sign`. -/
theorem fpFMAFinite_exact_cancel_sign_eq_policy {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RModePolicySpec R]
    (a b c : FiniteFp) (hsum : fmaAlignedSumInt a b c = 0) :
    fpFMAFinite a b c =
      Fp.finite
        ⟨if (a.s ^^ b.s) = c.s then (a.s ^^ b.s)
          else policyCancelSignOnExactZero (RModePolicyTag.kind (R := R)),
          FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩ := by
  rw [fpFMAFinite_exact_cancel_sign (a := a) (b := b) (c := c) hsum]
  simp [exactCancelSign_eq_policy (R := R)]

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

/-- Class-driven correctness for nonzero fused finite results. -/
theorem fpFMAFinite_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b c : FiniteFp)
    (hsum : (a.toVal : R) * b.toVal + c.toVal ≠ 0) :
    fpFMAFinite a b c = ○((a.toVal : R) * b.toVal + c.toVal) := by
  have hexact := fpFMAFinite_exact_sum R a b c
  set e_min := fmaEMin a b c with e_min_def
  set isum : ℤ := fmaAlignedSumInt a b c with isum_def
  have hsum_ne : isum ≠ 0 := by
    intro hzero
    apply hsum
    rw [hexact, hzero, Int.cast_zero, zero_mul]
  simp only [fpFMAFinite, e_min_def.symm]
  rw [if_neg hsum_ne]
  have hmag_ne : isum.natAbs ≠ 0 := by rwa [Int.natAbs_ne_zero]
  rw [roundIntSigM_correct_tc (R := R) _ _ _ hmag_ne]
  congr 1
  rw [intSigVal_eq_int_mul (R := R) hsum_ne, hexact]

/-! ## Commutativity -/

/-- `fpFMAFinite` is commutative in the first two operands. -/
theorem fpFMAFinite_comm_ab [RModeExec] (a b c : FiniteFp) :
    fpFMAFinite a b c = fpFMAFinite b a c := by
  simp only [fpFMAFinite, Bool.xor_comm a.s b.s, Nat.mul_comm a.m b.m, add_comm a.e b.e]

/-- `fpFMA` is commutative in the first two operands. -/
theorem fpFMA_comm_ab [RModeExec] (x y z : Fp) :
    fpFMA x y z = fpFMA y x z := by
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
theorem fpFMAFinite_neg_mul_neg [RModeExec] (a b c : FiniteFp) :
    fpFMAFinite (-a) (-b) c = fpFMAFinite a b c := by
  simp only [fpFMAFinite, FiniteFp.neg_def, Bool.not_xor_not]

/-- Negating both multiplicands in `fpFMA` is a no-op, since `(-x) × (-y) = x × y`. -/
theorem fpFMA_neg_mul_neg [RModeExec] (x y z : Fp) :
    fpFMA (-x) (-y) z = fpFMA x y z := by
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

/-- `fpFMAFinite a b 0 = fpMulFinite a b` when the product is nonzero.

This shows FMA generalizes multiplication: `round(a × b + 0) = round(a × b)`. -/
theorem fpFMAFinite_zero_eq_fpMulFinite {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a b : FiniteFp)
    (hprod : (a.toVal : R) * b.toVal ≠ 0) :
    fpFMAFinite a b 0 = a * b := by
  have hfma : fpFMAFinite a b 0 = ○((a.toVal : R) * b.toVal + (0 : FiniteFp).toVal) := by
    exact fpFMAFinite_correct (R := R) a b 0 (by rw [FiniteFp.toVal_zero, add_zero]; exact hprod)
  have hmul : a * b = ○((a.toVal : R) * b.toVal) := by
    exact fpMulFinite_correct (R := R) a b hprod
  rw [hfma, hmul, FiniteFp.toVal_zero, add_zero]

/-- `fpFMAFinite 1 a c = fpAddFinite a c` when the sum `a + c` is nonzero.

This shows FMA generalizes addition: `round(1 × a + c) = round(a + c)`. -/
theorem fpFMAFinite_one_eq_fpAddFinite {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
    (a c : FiniteFp)
    (hsum : (a.toVal : R) + c.toVal ≠ 0) :
    fpFMAFinite 1 a c = a + c := by
  have hfma : fpFMAFinite 1 a c = ○((1 : FiniteFp).toVal * (a.toVal : R) + c.toVal) := by
    exact fpFMAFinite_correct (R := R) 1 a c (by rw [FiniteFp.toVal_one, one_mul]; exact hsum)
  have hadd : a + c = ○((a.toVal : R) + c.toVal) := by
    exact fpAddFinite_correct (R := R) a c hsum
  rw [hfma, hadd, FiniteFp.toVal_one, one_mul]

end FMA
