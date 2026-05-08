import Flean.IntegerEquivalence.Basic

/-! # FP ↔ Integer equivalence: bit-pattern classifiers

Phase 1.5 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

Each `Fp`-level predicate (`isNaN`, `isInfinite`, `isFinite`) and FiniteFp
predicate (`isNormal`, `isSubnormal`, `isZero`) is decided by a single
bit-pattern test on the encoded `FloatBits`. This file lifts the existing
`FloatBits.isNaN` / `isInfinite` / etc. predicates to the abstract `Fp` level
via `ofBits`.

These bridges are the conceptual building blocks of IEEE 754 `fpClassify`:
the `(E.isZero, E.isAllOnes, T.isZero)` bit pattern uniquely classifies an
Fp into NaN / Inf / Zero / Subnormal / Normal.

`isPowerOfTwo` is a derived classifier: a normal Fp with all-zero trailing
significand has value `2^f.e` exactly — useful for compile-time
multiplication-by-power-of-two rewrites detected at runtime.
-/

namespace Fp

/-! ## Local decoding helpers (mirroring `Compare.lean`'s private versions) -/

private theorem FpExponent_eq_of_subnormal [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent = 0) :
    b.FpExponent = FloatFormat.min_exp := by
  rw [FloatBits.FpExponent_def, if_pos hE]

private theorem FpSignificand_eq_of_subnormal [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent = 0) :
    b.FpSignificand = b.toBitsTriple.significand.toNat := by
  rw [FloatBits.FpSignificand_def, if_pos hE]

/-! ## `Fp`-level classifier bridges

Each abstract `Fp` predicate lifts directly to the bit-level test on
`FloatBits` via the `ofBits` decoding. -/

/-- `Fp.isNaN` is exactly the bit-level NaN test. -/
@[simp] theorem isNaN_ofBits_iff [StdFloatFormat] (b : FloatBits) :
    (ofBits b).isNaN ↔ b.isNaN := by
  unfold Fp.isNaN ofBits
  constructor
  · intro h
    by_contra hb
    rw [dif_neg hb] at h
    split_ifs at h
  · intro hb; rw [dif_pos hb]

/-- `Fp.isInfinite` is exactly the bit-level infinity test. -/
@[simp] theorem isInfinite_ofBits_iff [StdFloatFormat] (b : FloatBits) :
    (ofBits b).isInfinite ↔ b.isInfinite := by
  unfold Fp.isInfinite ofBits
  constructor
  · intro h
    by_cases hb : b.isNaN
    · rw [dif_pos hb] at h
      rcases h with h | h <;> cases h
    · rw [dif_neg hb] at h
      by_cases hi : b.isInfinite
      · exact hi
      · rw [dif_neg hi] at h
        rcases h with h | h <;> cases h
  · intro hi
    have hn : ¬b.isNaN := FloatBits.isInfinite_notNaN b hi
    rw [dif_neg hn, dif_pos hi]
    cases h : b.sign <;> simp

/-- `Fp.isFinite` is exactly the bit-level finite test. -/
@[simp] theorem isFinite_ofBits_iff [StdFloatFormat] (b : FloatBits) :
    (ofBits b).isFinite ↔ b.isFinite := by
  unfold ofBits
  by_cases hn : b.isNaN
  · rw [dif_pos hn]
    have : ¬(Fp.NaN.isFinite) := Fp.isNaN_notFinite Fp.NaN Fp.NaN_isNaN
    have hbnf : ¬b.isFinite := FloatBits.isNaN_notFinite b hn
    exact iff_of_false this hbnf
  · by_cases hi : b.isInfinite
    · rw [dif_neg hn, dif_pos hi]
      have : ¬(Fp.infinite b.sign).isFinite :=
        Fp.isInfinite_notFinite _ (Fp.infinite_isInfinite _)
      have hbnf : ¬b.isFinite := FloatBits.isInfinite_notFinite b hi
      exact iff_of_false this hbnf
    · rw [dif_neg hn, dif_neg hi]
      have hf : b.isFinite := FloatBits.notNaN_notInfinite b hn hi
      exact iff_of_true (Fp.finite_isFinite _) hf

/-! ## FiniteFp-level classifier bridges (for decoded finite bit patterns)

For a bit-level finite `FloatBits`, decoding gives a FiniteFp whose
classification (`isNormal`/`isSubnormal`/`isZero`) is exactly the
corresponding bit-level test. -/

/-- Decoded `f.isNormal` is exactly the bit-level normal test
(under `b.isFinite`, the decoded `f.m` is in normal range iff `b.isNormal`). -/
theorem decoded_isNormal_iff [StdFloatFormat] (b : FloatBits) (hf : b.isFinite) :
    (⟨b.sign, b.FpExponent, b.FpSignificand,
        FloatBits.isFinite_validFloatVal hf⟩ : FiniteFp).isNormal
      ↔ b.isNormal := by
  show _root_.isNormal b.FpSignificand ↔ b.isNormal
  unfold FloatBits.isNormal
  -- Show: 2^(prec-1) ≤ FpSignificand ∧ FpSignificand < 2^prec ↔ E ≠ 0 ∧ ¬allOnes
  constructor
  · intro ⟨h_lo, _⟩
    -- 2^(prec-1) ≤ FpSignificand ⇒ E ≠ 0 (since if E = 0, FpSignificand = T < 2^sb)
    have hE_ne : b.toBitsTriple.exponent ≠ 0 := by
      intro hE
      rw [FloatBits.FpSignificand_def, if_pos hE] at h_lo
      have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
        b.toBitsTriple.significand.isLt
      have h_eq : (2 : ℕ) ^ FloatFormat.significandBits
                = 2 ^ (FloatFormat.prec - 1).toNat := by
        rw [FloatFormat.significandBits_eq]
      omega
    exact ⟨hE_ne, FloatBits.isFinite_exponent_not_allOnes b hf⟩
  · intro hn
    -- E ≠ 0, ¬allOnes ⇒ b is bit-level normal ⇒ FpSignificand has the leading 1
    constructor
    · -- 2^(prec-1) ≤ FpSignificand
      rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
        simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
      have hge := BitVec.toNat_ge_of_msb_true hmsb
      have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
        have := FloatFormat.significandBits_pos; omega
      rw [h_eq] at hge
      exact hge
    · -- FpSignificand < 2^prec
      rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have h_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
      exact h_lt.trans_eq (congr_arg (2 ^ ·) FloatFormat.one_plus_significandBits)

/-- Decoded `f.isSubnormal` is the broader value-level predicate that
includes zero (matches `IsValidFiniteVal`'s usage). It corresponds to
`b.toBitsTriple.exponent = 0` at the bit level — i.e., E=0 covers both
IEEE-subnormal (T≠0) and zero (T=0).

For the strict IEEE subnormal (excluding zero), see `decoded_isStrictSubnormal_iff`. -/
theorem decoded_isSubnormal_iff [StdFloatFormat] (b : FloatBits) (hf : b.isFinite) :
    (⟨b.sign, b.FpExponent, b.FpSignificand,
        FloatBits.isFinite_validFloatVal hf⟩ : FiniteFp).isSubnormal
      ↔ b.toBitsTriple.exponent = 0 := by
  show _root_.isSubnormal b.FpExponent b.FpSignificand ↔ _
  constructor
  · intro ⟨_, hm⟩
    by_contra hE
    -- E ≠ 0: FpSignificand ≥ 2^sb = 2^(prec-1) > m bound (subnormal)
    rw [FloatBits.FpSignificand_def, if_neg hE] at hm
    have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
      simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
    have hge := BitVec.toNat_ge_of_msb_true hmsb
    have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
      have := FloatFormat.significandBits_pos; omega
    rw [h_eq] at hge
    have h_pow_eq : (2 : ℕ) ^ FloatFormat.significandBits
                  = 2 ^ (FloatFormat.prec - 1).toNat := by
      rw [FloatFormat.significandBits_eq]
    rw [h_pow_eq] at hge
    have h_pow_pos : 0 < 2 ^ (FloatFormat.prec - 1).toNat :=
      Nat.pos_of_ne_zero (by positivity)
    omega
  · intro hE
    refine ⟨FpExponent_eq_of_subnormal hE, ?_⟩
    rw [FpSignificand_eq_of_subnormal hE]
    have := b.toBitsTriple.significand.isLt
    have h_pow_eq : (2 : ℕ) ^ FloatFormat.significandBits
                  = 2 ^ (FloatFormat.prec - 1).toNat := by
      rw [FloatFormat.significandBits_eq]
    omega

/-- Strict IEEE subnormal (decoded) is exactly the bit-level subnormal predicate
`FloatBits.isSubnormal = E=0 ∧ T≠0`. Excludes zero. -/
theorem decoded_isStrictSubnormal_iff [StdFloatFormat] (b : FloatBits)
    (hf : b.isFinite) :
    ((⟨b.sign, b.FpExponent, b.FpSignificand,
        FloatBits.isFinite_validFloatVal hf⟩ : FiniteFp).isSubnormal ∧
      ¬(⟨b.sign, b.FpExponent, b.FpSignificand,
          FloatBits.isFinite_validFloatVal hf⟩ : FiniteFp).isZero)
      ↔ b.isSubnormal := by
  unfold FloatBits.isSubnormal
  rw [decoded_isSubnormal_iff b hf]
  refine and_congr_right (fun hE => ?_)
  show ¬b.FpSignificand = 0 ↔ ¬b.isTSignificandZero
  unfold FloatBits.isTSignificandZero
  rw [FpSignificand_eq_of_subnormal hE]
  constructor
  · intro h h_T_eq
    apply h
    show b.toBitsTriple.significand.toNat = 0
    rw [h_T_eq]; rfl
  · intro h h_FS_eq
    apply h
    apply BitVec.eq_of_toNat_eq
    show b.toBitsTriple.significand.toNat = (0 : BitVec _).toNat
    simp [h_FS_eq]

/-- Decoded `f.isZero` is exactly the bit-level zero test
(`E = 0 ∧ T = 0`). Both sign bits encode zero (positive and negative zero). -/
theorem decoded_isZero_iff [StdFloatFormat] (b : FloatBits) (hf : b.isFinite) :
    (⟨b.sign, b.FpExponent, b.FpSignificand,
        FloatBits.isFinite_validFloatVal hf⟩ : FiniteFp).isZero
      ↔ b.isZero := by
  show b.FpSignificand = 0 ↔ b.isZero
  unfold FloatBits.isZero FloatBits.isTSignificandZero
  constructor
  · intro hm
    -- FpSignificand = 0. Cases on E.
    by_cases hE : b.toBitsTriple.exponent = 0
    · -- E = 0: FpSignificand = T.toNat = 0 ⇒ T = 0
      refine ⟨hE, ?_⟩
      apply BitVec.eq_of_toNat_eq
      show b.toBitsTriple.significand.toNat = (0 : BitVec _).toNat
      rw [FpSignificand_eq_of_subnormal hE] at hm
      simp [hm]
    · -- E ≠ 0: FpSignificand = 2^sb + T > 0, contradicts hm
      exfalso
      rw [FloatBits.FpSignificand_def, if_neg hE] at hm
      have hT_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
      have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
        simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
      have hge := BitVec.toNat_ge_of_msb_true hmsb
      have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
        have := FloatFormat.significandBits_pos; omega
      rw [h_eq] at hge
      have h_pow_pos : 0 < (2 : ℕ) ^ FloatFormat.significandBits :=
        Nat.pos_of_ne_zero (by positivity)
      omega
  · intro ⟨hE, hT⟩
    rw [FpSignificand_eq_of_subnormal hE]
    show b.toBitsTriple.significand.toNat = 0
    rw [hT]; rfl

/-! ## `isPowerOfTwo` classifier

A finite Fp is a power of two iff its decoded significand has exactly the
implicit leading 1 (trailing significand all zero) AND the biased exponent
is in normal range. The value is then exactly `2^f.e`. -/

/-- A non-negative `FiniteFp` represents a (positive) power of two. -/
def _root_.FiniteFp.isPositivePowerOfTwo [FloatFormat] (f : FiniteFp) : Prop :=
  f.s = false ∧ f.m = 2 ^ (FloatFormat.prec - 1).toNat

/-- For a normal non-negative bit pattern, the decoded `FiniteFp` is a positive
power of two iff the trailing significand is all zero. -/
theorem decoded_isPositivePowerOfTwo_iff [StdFloatFormat] (b : FloatBits)
    (hn : b.isNormal) (hs : b.sign = false) :
    (⟨b.sign, b.FpExponent, b.FpSignificand,
        FloatBits.isFinite_validFloatVal
          (FloatBits.notNaN_notInfinite b
            (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))⟩ : FiniteFp).isPositivePowerOfTwo
      ↔ b.toBitsTriple.significand = 0 := by
  unfold FiniteFp.isPositivePowerOfTwo
  rw [show (⟨b.sign, b.FpExponent, b.FpSignificand, _⟩ : FiniteFp).s = b.sign from rfl,
      show (⟨b.sign, b.FpExponent, b.FpSignificand, _⟩ : FiniteFp).m = b.FpSignificand from rfl]
  -- LHS: b.sign = false ∧ FpSignificand = 2^(prec-1).toNat
  -- RHS: T = 0
  rw [FloatBits.FpSignificand_def, if_neg hn.1]
  constructor
  · rintro ⟨_, hm⟩
    -- (BitVec.ofBool true ++ T).toNat = 2^(prec-1).toNat means T.toNat = 0
    apply BitVec.eq_of_toNat_eq
    show b.toBitsTriple.significand.toNat = (0 : BitVec _).toNat
    have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
      b.toBitsTriple.significand.isLt
    -- (BitVec.ofBool true ++ T).toNat = 2^sb + T.toNat
    have h_decomp : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).toNat
                  = 2 ^ FloatFormat.significandBits + b.toBitsTriple.significand.toNat := by
      rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
      show (BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
          + b.toBitsTriple.significand.toNat = _
      simp
    rw [h_decomp] at hm
    have h_pow_eq : (2 : ℕ) ^ FloatFormat.significandBits
                  = 2 ^ (FloatFormat.prec - 1).toNat := by
      rw [FloatFormat.significandBits_eq]
    simp [show b.toBitsTriple.significand.toNat = 0 from by omega]
  · intro hT
    refine ⟨hs, ?_⟩
    rw [hT]
    show ((BitVec.ofBool true) ++ (0 : BitVec _)).toNat = 2 ^ (FloatFormat.prec - 1).toNat
    have h_pow_eq : (2 : ℕ) ^ FloatFormat.significandBits
                  = 2 ^ (FloatFormat.prec - 1).toNat := by
      rw [FloatFormat.significandBits_eq]
    rw [BitVec.toNat_append]
    simp [Nat.shiftLeft_eq]

end Fp
