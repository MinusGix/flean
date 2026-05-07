import Flean.IntegerEquivalence.Basic
import Flean.Order

/-! # FP ↔ Integer equivalence: comparison ↔ bit comparison

Phase 2 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

For two non-negative non-NaN `Fp` values, the IEEE 754 ordering on `Fp` agrees
with unsigned integer ordering on the underlying bit pattern. This is by design
— the standard layout `[sign][biased exponent][trailing significand]` makes the
bit pattern monotonically non-decreasing in value for non-negative inputs.

The matching property for non-positive inputs has the order reversed (since
the sign bit dominates the bit value). Same-sign comparisons are the cleanest
case and the most useful in practice (e.g. argmax for softmax).

## Layered structure

1. **Bit decomposition** (`b_toNat_eq_triple`): the underlying `b.b.toNat` is a
   weighted sum of the sign / exponent / trailing-significand fields.
2. **Same-sign reduction** (`b_toNat_lt_iff_of_same_sign`): two same-sign bit
   patterns satisfy `b₁.b.toNat < b₂.b.toNat` iff the `(E, T)` pairs are
   lex-less in the unsigned-integer sense.
3. **Bridge** (TBD): for non-negative finite inputs, the FP `<` agrees with
   the bit comparison.
-/

namespace Fp

namespace FloatBits

variable [FloatFormat]

/-! ## Bit decomposition: `b.b.toNat` from the triple -/

/-- Decompose `b.b.toNat` along the `[sign][exponent][trailing-significand]`
field layout. The sign contributes `sign · 2^(expBits + sigBits)`, the
biased exponent contributes `E · 2^sigBits`, and the trailing significand
contributes itself. -/
theorem b_toNat_eq_triple (b : FloatBits) :
    b.b.toNat
      = b.toBitsTriple.sign.toNat
          * 2 ^ (FloatFormat.exponentBits + FloatFormat.significandBits)
        + b.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
        + b.toBitsTriple.significand.toNat := by
  -- Use round-trip: b = mk' sign exp sig, and mk' constructs via concatenation
  have h_mk : b = FloatBits.mk' b.toBitsTriple.sign b.toBitsTriple.exponent
                  b.toBitsTriple.significand := by
    apply appendToBitsTriple_eq b.toBitsTriple b rfl
  set s := b.toBitsTriple.sign
  set E := b.toBitsTriple.exponent
  set T := b.toBitsTriple.significand
  -- mk' s E T has b = (s ++ E ++ T).cast _ : BitVec bitSize
  -- Its toNat: use BitVec.toNat_append twice.
  have h_b : b.b = ((s ++ E ++ T).cast FloatFormat.bitSize_eq.symm) := by
    rw [h_mk]; rfl
  have hT_lt : T.toNat < 2 ^ FloatFormat.significandBits := T.isLt
  have hE_lt : E.toNat < 2 ^ FloatFormat.exponentBits := E.isLt
  rw [h_b, BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt hT_lt,
      ← Nat.shiftLeft_add_eq_or_of_lt hE_lt]
  simp only [Nat.shiftLeft_eq, pow_add]
  ring

/-! ## Same-sign reduction: bit comparison ↔ `(E, T)` lex -/

/-- For two same-sign bit patterns, comparing `b.b.toNat` reduces to the
unsigned `(exponent, significand)` lex pair. -/
theorem b_toNat_lt_iff_of_same_sign (b₁ b₂ : FloatBits)
    (hs : b₁.toBitsTriple.sign = b₂.toBitsTriple.sign) :
    b₁.b.toNat < b₂.b.toNat
      ↔ b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
          + b₁.toBitsTriple.significand.toNat
        < b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
          + b₂.toBitsTriple.significand.toNat := by
  rw [b_toNat_eq_triple b₁, b_toNat_eq_triple b₂, hs]
  omega

/-- Lex form: same-sign bit comparison decomposes into "exponent strictly less,
or exponent equal and significand strictly less". -/
theorem b_toNat_lt_iff_lex_of_same_sign (b₁ b₂ : FloatBits)
    (hs : b₁.toBitsTriple.sign = b₂.toBitsTriple.sign)
    (hT₁ : b₁.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits)
    (hT₂ : b₂.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits) :
    b₁.b.toNat < b₂.b.toNat
      ↔ b₁.toBitsTriple.exponent.toNat < b₂.toBitsTriple.exponent.toNat
        ∨ (b₁.toBitsTriple.exponent.toNat = b₂.toBitsTriple.exponent.toNat
            ∧ b₁.toBitsTriple.significand.toNat < b₂.toBitsTriple.significand.toNat) := by
  rw [b_toNat_lt_iff_of_same_sign b₁ b₂ hs]
  set E₁ := b₁.toBitsTriple.exponent.toNat
  set E₂ := b₂.toBitsTriple.exponent.toNat
  set T₁ := b₁.toBitsTriple.significand.toNat
  set T₂ := b₂.toBitsTriple.significand.toNat
  set p := (2 : ℕ) ^ FloatFormat.significandBits with hp_def
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (by positivity)
  constructor
  · intro h
    by_cases hE : E₁ = E₂
    · right; refine ⟨hE, ?_⟩; rw [hE] at h; linarith
    · left
      by_contra hge
      push_neg at hge
      -- E₁ ≥ E₂ but E₁ ≠ E₂, so E₂ < E₁
      have hE_lt : E₂ < E₁ := lt_of_le_of_ne hge (Ne.symm hE)
      have : (E₂ + 1) * p ≤ E₁ * p :=
        Nat.mul_le_mul_right p (Nat.succ_le_of_lt hE_lt)
      linarith
  · rintro (hE | ⟨hE_eq, hT⟩)
    · -- E₁ < E₂: (E₁ + 1) * p ≤ E₂ * p, and T₁ < p
      have : (E₁ + 1) * p ≤ E₂ * p :=
        Nat.mul_le_mul_right p (Nat.succ_le_of_lt hE)
      linarith
    · rw [hE_eq]; linarith

end FloatBits

/-! ## `is_mag_lt` on normal FiniteFp's reduces to `(e, m)` lex -/

/-- For two normal-significand `FiniteFp`s, `is_mag_lt` agrees with the
lexicographic order on `(e, m)`: smaller exponent always wins, ties on
exponent reduce to significand comparison.

The "smaller exponent always wins" direction crucially uses normality of both
significands: `m * 2^k ≥ 2^(prec-1) * 2 = 2^prec > m'` for any normal `m`
and `m' < 2^prec`, so cross-binade comparisons are decided by exponent alone. -/
theorem FiniteFp.is_mag_lt_iff_lex_of_normal [FloatFormat] {f₁ f₂ : FiniteFp}
    (hn₁ : _root_.isNormal f₁.m) (hn₂ : _root_.isNormal f₂.m) :
    f₁.is_mag_lt f₂ ↔ f₁.e < f₂.e ∨ (f₁.e = f₂.e ∧ f₁.m < f₂.m) := by
  unfold FiniteFp.is_mag_lt
  -- Bounds from normality
  have hprec := FloatFormat.valid_prec
  have hprec_eq : (FloatFormat.prec - 1).toNat + 1 = FloatFormat.prec.toNat := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]; omega
  have hm₁_lo : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f₁.m := hn₁.1
  have hm₂_lo : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f₂.m := hn₂.1
  have hm₁_hi : f₁.m < (2 : ℕ) ^ FloatFormat.prec.toNat := hn₁.2
  have hm₂_hi : f₂.m < (2 : ℕ) ^ FloatFormat.prec.toNat := hn₂.2
  have h_pow_eq : (2 : ℕ) ^ FloatFormat.prec.toNat
                = 2 * 2 ^ (FloatFormat.prec - 1).toNat := by
    conv_lhs => rw [← hprec_eq]
    rw [pow_succ]; ring
  split_ifs with h_eq h_gt
  · -- e₁ = e₂: is_mag_lt = m₁ < m₂; lex = (e₁ = e₂ ∧ m₁ < m₂)
    constructor
    · intro h; exact Or.inr ⟨h_eq, h⟩
    · rintro (h | ⟨_, h⟩)
      · exfalso; omega
      · exact h
  · -- e₁ > e₂: is_mag_lt = m₁ * 2^k < m₂; need to show this is false, lex is false too
    constructor
    · -- is_mag_lt holds → contradiction
      intro h
      have hk : 1 ≤ (f₁.e - f₂.e).natAbs := by
        rcases Int.natAbs_eq (f₁.e - f₂.e) with h1 | h1 <;> omega
      have h_2_le_pow : (2 : ℕ) ≤ 2 ^ (f₁.e - f₂.e).natAbs := by
        calc (2 : ℕ) = 2 ^ 1 := by ring
          _ ≤ 2 ^ (f₁.e - f₂.e).natAbs :=
              Nat.pow_le_pow_right (n := 2) (by norm_num) hk
      have hm₁_pow : (2 : ℕ) * 2 ^ (FloatFormat.prec - 1).toNat
                  ≤ f₁.m * 2 ^ (f₁.e - f₂.e).natAbs := by
        calc (2 : ℕ) * 2 ^ (FloatFormat.prec - 1).toNat
              ≤ 2 ^ (f₁.e - f₂.e).natAbs * 2 ^ (FloatFormat.prec - 1).toNat :=
                Nat.mul_le_mul_right _ h_2_le_pow
          _ ≤ 2 ^ (f₁.e - f₂.e).natAbs * f₁.m :=
                Nat.mul_le_mul_left _ hm₁_lo
          _ = f₁.m * 2 ^ (f₁.e - f₂.e).natAbs := by ring
      omega
    · rintro (h | ⟨h, _⟩) <;> omega
  · -- e₁ < e₂
    have h_lt : f₁.e < f₂.e := by push_neg at h_eq h_gt; omega
    have hk : 1 ≤ (f₂.e - f₁.e).natAbs := by
      rcases Int.natAbs_eq (f₂.e - f₁.e) with h1 | h1 <;> omega
    have h_2_le_pow : (2 : ℕ) ≤ 2 ^ (f₂.e - f₁.e).natAbs := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (f₂.e - f₁.e).natAbs :=
            Nat.pow_le_pow_right (n := 2) (by norm_num) hk
    have h_pow_ge : (2 : ℕ) * 2 ^ (FloatFormat.prec - 1).toNat
                  ≤ f₂.m * 2 ^ (f₂.e - f₁.e).natAbs := by
      calc (2 : ℕ) * 2 ^ (FloatFormat.prec - 1).toNat
            ≤ 2 ^ (f₂.e - f₁.e).natAbs * 2 ^ (FloatFormat.prec - 1).toNat :=
              Nat.mul_le_mul_right _ h_2_le_pow
        _ ≤ 2 ^ (f₂.e - f₁.e).natAbs * f₂.m :=
              Nat.mul_le_mul_left _ hm₂_lo
        _ = f₂.m * 2 ^ (f₂.e - f₁.e).natAbs := by ring
    constructor
    · intro _; exact Or.inl h_lt
    · intros _; omega

/-! ## Decoding helpers for bit-normal `FloatBits`

Shared infrastructure between the non-negative and non-positive bridges. -/

/-- Bit-level normal `b` has `FpSignificand` in the value-level normal range. -/
private theorem isNormal_FpSignificand_of_isNormal [StdFloatFormat] {b : FloatBits}
    (hn : b.isNormal) :
    _root_.isNormal b.FpSignificand := by
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

/-- For bit-normal `b`, `FpExponent = E.toNat - exponentBias`. -/
private theorem FpExponent_eq_of_normal [FloatFormat] {b : FloatBits}
    (hn : b.isNormal) :
    b.FpExponent = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := by
  rw [FloatBits.FpExponent_def, if_neg hn.1]

/-- For non-zero biased exponent (covers both bit-normal and bit-infinity),
`FpSignificand = 2^sigBits + T.toNat`. -/
private theorem FpSignificand_eq_of_E_ne_zero [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent ≠ 0) :
    b.FpSignificand
      = 2 ^ FloatFormat.significandBits + b.toBitsTriple.significand.toNat := by
  rw [FloatBits.FpSignificand_def, if_neg hE]
  have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b.toBitsTriple.significand.isLt
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
  show (BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
      + b.toBitsTriple.significand.toNat = _
  simp

/-- For bit-normal `b`, `FpSignificand = 2^sigBits + T.toNat`. -/
private theorem FpSignificand_eq_of_normal [FloatFormat] {b : FloatBits}
    (hn : b.isNormal) :
    b.FpSignificand
      = 2 ^ FloatFormat.significandBits + b.toBitsTriple.significand.toNat :=
  FpSignificand_eq_of_E_ne_zero hn.1

/-- For bit-subnormal `b` (`E = 0`), `FpExponent = min_exp`. -/
private theorem FpExponent_eq_of_subnormal [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent = 0) :
    b.FpExponent = FloatFormat.min_exp := by
  rw [FloatBits.FpExponent_def, if_pos hE]

/-- For bit-subnormal `b` (`E = 0`), `FpSignificand = T.toNat`. -/
private theorem FpSignificand_eq_of_subnormal [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent = 0) :
    b.FpSignificand = b.toBitsTriple.significand.toNat := by
  rw [FloatBits.FpSignificand_def, if_pos hE]

/-- For bit-subnormal `b`, `FpSignificand` is bounded above by `2^sigBits`. -/
private theorem FpSignificand_lt_pow_of_subnormal [FloatFormat] {b : FloatBits}
    (hE : b.toBitsTriple.exponent = 0) :
    b.FpSignificand < 2 ^ FloatFormat.significandBits := by
  rw [FpSignificand_eq_of_subnormal hE]
  exact b.toBitsTriple.significand.isLt

/-- Decoding `b : FloatBits` to its `Fp.finite` form when `b` is bit-finite. -/
private theorem ofBits_eq_finite_of_isFinite [StdFloatFormat] (b : FloatBits)
    (hf : b.isFinite) :
    ofBits b = Fp.finite ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal hf⟩ := by
  have hni : ¬b.isNaN := hf.1
  have hii : ¬b.isInfinite := hf.2
  have h_step : ofBits b = Fp.finite ⟨b.toBitsTriple.sign.toNat == 1,
      b.FpExponent, b.FpSignificand, FloatBits.isFinite_validFloatVal hf⟩ := by
    unfold ofBits; rw [dif_neg hni, dif_neg hii]
  rw [h_step]
  congr 1; apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, rfl, rfl⟩
  show (b.toBitsTriple.sign.toNat == 1) = b.sign
  unfold FloatBits.sign
  rcases BitVec.one_or b.toBitsTriple.sign with h | h <;> rw [h] <;> rfl

/-- Decoding `b : FloatBits` to its `Fp.finite` form for a bit-normal `b`. -/
private theorem ofBits_eq_finite_of_normal [StdFloatFormat] (b : FloatBits)
    (hn : b.isNormal) :
    ofBits b = Fp.finite ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal
        (FloatBits.notNaN_notInfinite b
          (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))⟩ :=
  ofBits_eq_finite_of_isFinite b
    (FloatBits.notNaN_notInfinite b
      (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))

/-! ## Main bridge: FP `<` ↔ unsigned bit comparison (non-negative bit-normal) -/

/-- **Phase 2 main bridge (non-negative).** For two non-negative bit-level
normal `FloatBits`, the IEEE 754 `Fp` ordering on `ofBits` agrees with
unsigned integer comparison on the underlying bit pattern. -/
theorem ofBits_lt_iff_b_toNat_lt_of_normal_nonneg
    [StdFloatFormat] (b₁ b₂ : FloatBits)
    (hn₁ : b₁.isNormal) (hn₂ : b₂.isNormal)
    (hs₁ : b₁.sign = false) (hs₂ : b₂.sign = false) :
    ofBits b₁ < ofBits b₂ ↔ b₁.b.toNat < b₂.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal (FloatBits.notNaN_notInfinite b₁
      (fun ⟨h, _⟩ => hn₁.2 h) (fun ⟨h, _⟩ => hn₁.2 h))⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal (FloatBits.notNaN_notInfinite b₂
      (fun ⟨h, _⟩ => hn₂.2 h) (fun ⟨h, _⟩ => hn₂.2 h))⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_normal b₁ hn₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_normal b₂ hn₂
  have hf₁_normal : _root_.isNormal f₁.m :=
    isNormal_FpSignificand_of_isNormal hn₁
  have hf₂_normal : _root_.isNormal f₂.m :=
    isNormal_FpSignificand_of_isNormal hn₂
  rw [hofb₁, hofb₂]
  show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) ↔ b₁.b.toNat < b₂.b.toNat
  rw [show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) = (f₁ < f₂) from rfl]
  -- Both positive: f₁ < f₂ ↔ is_mag_lt f₁ f₂
  have h_lt_iff : f₁ < f₂ ↔ f₁.is_mag_lt f₂ := by
    rw [FiniteFp.lt_def]
    have h₁ : f₁.s = false := hs₁
    have h₂ : f₂.s = false := hs₂
    simp [h₁, h₂]
  rw [h_lt_iff, FiniteFp.is_mag_lt_iff_lex_of_normal hf₁_normal hf₂_normal]
  show f₁.e < f₂.e ∨ (f₁.e = f₂.e ∧ f₁.m < f₂.m) ↔ b₁.b.toNat < b₂.b.toNat
  -- Same sign at BV level: both are 0#1
  have hsbv : b₁.toBitsTriple.sign = b₂.toBitsTriple.sign := by
    have h1 : b₁.toBitsTriple.sign = 0#1 := by
      unfold FloatBits.sign at hs₁
      rcases BitVec.one_or b₁.toBitsTriple.sign with h | h
      · exact h
      · rw [h] at hs₁; simp at hs₁
    have h2 : b₂.toBitsTriple.sign = 0#1 := by
      unfold FloatBits.sign at hs₂
      rcases BitVec.one_or b₂.toBitsTriple.sign with h | h
      · exact h
      · rw [h] at hs₂; simp at hs₂
    rw [h1, h2]
  rw [FloatBits.b_toNat_lt_iff_lex_of_same_sign b₁ b₂ hsbv
        b₁.toBitsTriple.significand.isLt
        b₂.toBitsTriple.significand.isLt]
  rw [show f₁.e = b₁.FpExponent from rfl, show f₂.e = b₂.FpExponent from rfl,
      show f₁.m = b₁.FpSignificand from rfl, show f₂.m = b₂.FpSignificand from rfl,
      FpExponent_eq_of_normal hn₁, FpExponent_eq_of_normal hn₂,
      FpSignificand_eq_of_normal hn₁, FpSignificand_eq_of_normal hn₂]
  constructor
  · rintro (h | ⟨he, hm⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩
  · rintro (h | ⟨he, hm⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩

/-- **Phase 2 main bridge (non-positive).** For two non-positive bit-level
normal `FloatBits`, IEEE 754 `Fp` ordering on `ofBits` is *anti-monotone* in
the bit pattern: larger magnitude ⇒ larger bits ⇒ more negative ⇒ smaller value.
-/
theorem ofBits_lt_iff_b_toNat_gt_of_normal_nonpos
    [StdFloatFormat] (b₁ b₂ : FloatBits)
    (hn₁ : b₁.isNormal) (hn₂ : b₂.isNormal)
    (hs₁ : b₁.sign = true) (hs₂ : b₂.sign = true) :
    ofBits b₁ < ofBits b₂ ↔ b₂.b.toNat < b₁.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal (FloatBits.notNaN_notInfinite b₁
      (fun ⟨h, _⟩ => hn₁.2 h) (fun ⟨h, _⟩ => hn₁.2 h))⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal (FloatBits.notNaN_notInfinite b₂
      (fun ⟨h, _⟩ => hn₂.2 h) (fun ⟨h, _⟩ => hn₂.2 h))⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_normal b₁ hn₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_normal b₂ hn₂
  have hf₁_normal : _root_.isNormal f₁.m :=
    isNormal_FpSignificand_of_isNormal hn₁
  have hf₂_normal : _root_.isNormal f₂.m :=
    isNormal_FpSignificand_of_isNormal hn₂
  rw [hofb₁, hofb₂]
  show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) ↔ b₂.b.toNat < b₁.b.toNat
  rw [show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) = (f₁ < f₂) from rfl]
  -- Both negative: f₁ < f₂ ↔ is_mag_lt f₂ f₁ (REVERSED)
  have h_lt_iff : f₁ < f₂ ↔ f₂.is_mag_lt f₁ := by
    rw [FiniteFp.lt_def]
    have h₁ : f₁.s = true := hs₁
    have h₂ : f₂.s = true := hs₂
    simp [h₁, h₂]
  rw [h_lt_iff, FiniteFp.is_mag_lt_iff_lex_of_normal hf₂_normal hf₁_normal]
  show f₂.e < f₁.e ∨ (f₂.e = f₁.e ∧ f₂.m < f₁.m) ↔ b₂.b.toNat < b₁.b.toNat
  -- Same sign at BV level: both are 1#1
  have hsbv : b₂.toBitsTriple.sign = b₁.toBitsTriple.sign := by
    have h1 : b₁.toBitsTriple.sign = 1#1 := by
      unfold FloatBits.sign at hs₁
      rcases BitVec.one_or b₁.toBitsTriple.sign with h | h
      · rw [h] at hs₁; simp at hs₁
      · exact h
    have h2 : b₂.toBitsTriple.sign = 1#1 := by
      unfold FloatBits.sign at hs₂
      rcases BitVec.one_or b₂.toBitsTriple.sign with h | h
      · rw [h] at hs₂; simp at hs₂
      · exact h
    rw [h1, h2]
  rw [FloatBits.b_toNat_lt_iff_lex_of_same_sign b₂ b₁ hsbv
        b₂.toBitsTriple.significand.isLt
        b₁.toBitsTriple.significand.isLt]
  rw [show f₁.e = b₁.FpExponent from rfl, show f₂.e = b₂.FpExponent from rfl,
      show f₁.m = b₁.FpSignificand from rfl, show f₂.m = b₂.FpSignificand from rfl,
      FpExponent_eq_of_normal hn₁, FpExponent_eq_of_normal hn₂,
      FpSignificand_eq_of_normal hn₁, FpSignificand_eq_of_normal hn₂]
  constructor
  · rintro (h | ⟨he, hm⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩
  · rintro (h | ⟨he, hm⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩

/-! ## Subnormal-tolerant Phase 2 bridge (non-negative case)

Generalizes `ofBits_lt_iff_b_toNat_lt_of_normal_nonneg` to allow any
non-negative finite `FloatBits` (subnormal or normal). The key arithmetic
fact: in standard formats `min_exp + bias = 1`, so the smallest normal
binade (E=1) and the subnormal binade (E=0) share `f.e = min_exp`. The
significand bound transition `T < 2^sb ≤ 2^sb + T'` makes the lex
comparison agree with the FP value comparison across the boundary. -/

section SubnormalTolerant
variable [StdFloatFormat]

/-- Decoded `f.e` for non-zero biased exponent. -/
private theorem FpExponent_eq_of_E_ne_zero {b : FloatBits}
    (hE : b.toBitsTriple.exponent ≠ 0) :
    b.FpExponent = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := by
  rw [FloatBits.FpExponent_def, if_neg hE]

/-- Standard format relation: `min_exp + bias = 1`. -/
private theorem min_exp_plus_bias_eq_one :
    FloatFormat.min_exp + FloatFormat.exponentBias = 1 := by
  have := StdFloatFormat.st
  unfold FloatFormat.isStandardExpRange at this
  unfold FloatFormat.exponentBias; omega

/-- `2 * 2^sigBits = 2^prec`, the basic format identity. -/
private theorem two_mul_pow_sigBits_eq_pow_prec :
    2 * 2 ^ FloatFormat.significandBits = 2 ^ FloatFormat.prec.toNat := by
  have hprec_eq : (FloatFormat.prec - 1).toNat + 1 = FloatFormat.prec.toNat := by
    rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
    have := FloatFormat.valid_prec; omega
  show 2 * 2 ^ (FloatFormat.prec - 1).toNat = _
  conv_rhs => rw [← hprec_eq]
  rw [pow_succ]; ring

/-! ### The four (E vs 0) sub-cases of `is_mag_lt ↔ bit_lt` -/

/-- (sub, sub): same e = min_exp, m = T. Comparison reduces to T comparison. -/
private theorem is_mag_lt_iff_bit_sub_sub
    {b₁ b₂ : FloatBits} (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hZ₁ : b₁.toBitsTriple.exponent = 0) (hZ₂ : b₂.toBitsTriple.exponent = 0) :
    (⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).is_mag_lt
    ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₂⟩ ↔
      b₁.toBitsTriple.significand.toNat < b₂.toBitsTriple.significand.toNat := by
  have he₁ := FpExponent_eq_of_subnormal hZ₁
  have he₂ := FpExponent_eq_of_subnormal hZ₂
  have hm₁ := FpSignificand_eq_of_subnormal hZ₁
  have hm₂ := FpSignificand_eq_of_subnormal hZ₂
  unfold FiniteFp.is_mag_lt
  show (if b₁.FpExponent = b₂.FpExponent then b₁.FpSignificand < b₂.FpSignificand
        else _) ↔ _
  rw [if_pos (he₁.trans he₂.symm), hm₁, hm₂]

/-- (sub, norm): always TRUE. f₁.m = T₁ < 2^sb ≤ p + T₂ ≤ f₂.m * 2^k. -/
private theorem is_mag_lt_iff_bit_sub_norm
    {b₁ b₂ : FloatBits} (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hZ₁ : b₁.toBitsTriple.exponent = 0) (hZ₂ : b₂.toBitsTriple.exponent ≠ 0) :
    (⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).is_mag_lt
    ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₂⟩ := by
  have he₁ : b₁.FpExponent = FloatFormat.min_exp := FpExponent_eq_of_subnormal hZ₁
  have he₂ : b₂.FpExponent
      = (b₂.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias :=
    FpExponent_eq_of_E_ne_zero hZ₂
  have hm₁ : b₁.FpSignificand = b₁.toBitsTriple.significand.toNat :=
    FpSignificand_eq_of_subnormal hZ₁
  have hm₂ : b₂.FpSignificand
      = 2 ^ FloatFormat.significandBits + b₂.toBitsTriple.significand.toNat :=
    FpSignificand_eq_of_E_ne_zero hZ₂
  have hT₁_lt : b₁.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b₁.toBitsTriple.significand.isLt
  have hE₂_pos : 0 < b₂.toBitsTriple.exponent.toNat := by
    rw [Nat.pos_iff_ne_zero]; intro h
    exact hZ₂ (BitVec.eq_of_toNat_eq h)
  have h_min : FloatFormat.min_exp + FloatFormat.exponentBias = 1 := min_exp_plus_bias_eq_one
  have h_2p : 2 * 2 ^ FloatFormat.significandBits = 2 ^ FloatFormat.prec.toNat :=
    two_mul_pow_sigBits_eq_pow_prec
  unfold FiniteFp.is_mag_lt
  show (if b₁.FpExponent = b₂.FpExponent then b₁.FpSignificand < b₂.FpSignificand
        else if b₁.FpExponent > b₂.FpExponent then _
        else b₁.FpSignificand < b₂.FpSignificand
              * 2 ^ (b₂.FpExponent - b₁.FpExponent).natAbs)
  -- f₁.e ≤ f₂.e always (since f₁.e = min_exp = 1 - bias ≤ E₂ - bias = f₂.e for E₂ ≥ 1)
  have h_e_le : b₁.FpExponent ≤ b₂.FpExponent := by
    rw [he₁, he₂]; omega
  by_cases h_eq : b₁.FpExponent = b₂.FpExponent
  · rw [if_pos h_eq, hm₁, hm₂]; omega
  · rw [if_neg h_eq]
    have h_lt : b₁.FpExponent < b₂.FpExponent := lt_of_le_of_ne h_e_le h_eq
    rw [if_neg (not_lt.mpr (le_of_lt h_lt)), hm₁, hm₂]
    -- T₁ < (p + T₂) * 2^k. T₁ < p ≤ p + T₂ ≤ (p + T₂) * 1 ≤ (p + T₂) * 2^k.
    have hk : 1 ≤ (b₂.FpExponent - b₁.FpExponent).natAbs := by
      rcases Int.natAbs_eq (b₂.FpExponent - b₁.FpExponent) with heq | heq <;> omega
    have h_pow_pos : 1 ≤ 2 ^ (b₂.FpExponent - b₁.FpExponent).natAbs :=
      Nat.one_le_two_pow
    have : (2 ^ FloatFormat.significandBits + b₂.toBitsTriple.significand.toNat)
        ≤ (2 ^ FloatFormat.significandBits + b₂.toBitsTriple.significand.toNat)
            * 2 ^ (b₂.FpExponent - b₁.FpExponent).natAbs := by
      nlinarith [h_pow_pos]
    omega

/-- (norm, sub): always FALSE. f₁.m = p + T₁ ≥ p > T₂ = f₂.m, etc. -/
private theorem not_is_mag_lt_norm_sub
    {b₁ b₂ : FloatBits} (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hZ₁ : b₁.toBitsTriple.exponent ≠ 0) (hZ₂ : b₂.toBitsTriple.exponent = 0) :
    ¬(⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).is_mag_lt
    ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
        FloatBits.isFinite_validFloatVal hf₂⟩ := by
  have he₁ : b₁.FpExponent
      = (b₁.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias :=
    FpExponent_eq_of_E_ne_zero hZ₁
  have he₂ : b₂.FpExponent = FloatFormat.min_exp := FpExponent_eq_of_subnormal hZ₂
  have hm₁ : b₁.FpSignificand
      = 2 ^ FloatFormat.significandBits + b₁.toBitsTriple.significand.toNat :=
    FpSignificand_eq_of_E_ne_zero hZ₁
  have hm₂ : b₂.FpSignificand = b₂.toBitsTriple.significand.toNat :=
    FpSignificand_eq_of_subnormal hZ₂
  have hT₂_lt : b₂.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b₂.toBitsTriple.significand.isLt
  have hE₁_pos : 0 < b₁.toBitsTriple.exponent.toNat := by
    rw [Nat.pos_iff_ne_zero]; intro h; exact hZ₁ (BitVec.eq_of_toNat_eq h)
  have h_min : FloatFormat.min_exp + FloatFormat.exponentBias = 1 := min_exp_plus_bias_eq_one
  have h_2p : 2 * 2 ^ FloatFormat.significandBits = 2 ^ FloatFormat.prec.toNat :=
    two_mul_pow_sigBits_eq_pow_prec
  unfold FiniteFp.is_mag_lt
  show ¬(if b₁.FpExponent = b₂.FpExponent then b₁.FpSignificand < b₂.FpSignificand
         else if b₁.FpExponent > b₂.FpExponent then b₁.FpSignificand
            * 2 ^ (b₁.FpExponent - b₂.FpExponent).natAbs < b₂.FpSignificand
         else _)
  have h_e_ge : b₂.FpExponent ≤ b₁.FpExponent := by
    rw [he₁, he₂]; omega
  by_cases h_eq : b₁.FpExponent = b₂.FpExponent
  · rw [if_pos h_eq, hm₁, hm₂]; omega
  · rw [if_neg h_eq]
    have h_gt : b₂.FpExponent < b₁.FpExponent := lt_of_le_of_ne h_e_ge (Ne.symm h_eq)
    rw [if_pos h_gt, hm₁, hm₂]
    -- (p + T₁) * 2^k < T₂ but T₂ < p ≤ p + T₁ ≤ (p + T₁) * 2^k.
    have h_pow_pos : 1 ≤ 2 ^ (b₁.FpExponent - b₂.FpExponent).natAbs :=
      Nat.one_le_two_pow
    have : (2 ^ FloatFormat.significandBits + b₁.toBitsTriple.significand.toNat)
        ≤ (2 ^ FloatFormat.significandBits + b₁.toBitsTriple.significand.toNat)
            * 2 ^ (b₁.FpExponent - b₂.FpExponent).natAbs := by
      nlinarith [h_pow_pos]
    omega

/-! ### Combined: `is_mag_lt ↔ bit_lt` for any non-negative finite -/

/-- Substantive lemma: for any two non-negative-finite-decoded FiniteFps,
`is_mag_lt` reduces to additive `(E, T)` comparison on bit fields.
Combines the four (E vs 0) sub-cases. -/
private theorem is_mag_lt_iff_b_E_T_lt_of_finite
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite) :
    (⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).is_mag_lt
    ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₂⟩ ↔
      b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
        + b₁.toBitsTriple.significand.toNat
      < b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
        + b₂.toBitsTriple.significand.toNat := by
  -- Use abbreviations for readability without `set`
  have hp_pos : 0 < (2 : ℕ) ^ FloatFormat.significandBits :=
    Nat.pos_of_ne_zero (by positivity)
  have hT₁_lt : b₁.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b₁.toBitsTriple.significand.isLt
  have hT₂_lt : b₂.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b₂.toBitsTriple.significand.isLt
  by_cases hZ₁ : b₁.toBitsTriple.exponent = 0
  · have hE₁_zero : b₁.toBitsTriple.exponent.toNat = 0 := by rw [hZ₁]; rfl
    by_cases hZ₂ : b₂.toBitsTriple.exponent = 0
    · -- (sub, sub)
      have hE₂_zero : b₂.toBitsTriple.exponent.toNat = 0 := by rw [hZ₂]; rfl
      rw [is_mag_lt_iff_bit_sub_sub hf₁ hf₂ hZ₁ hZ₂, hE₁_zero, hE₂_zero]
      simp
    · -- (sub, norm): always TRUE
      have hE₂_pos : 0 < b₂.toBitsTriple.exponent.toNat := by
        rw [Nat.pos_iff_ne_zero]; intro h
        exact hZ₂ (BitVec.eq_of_toNat_eq h)
      have h_lt := is_mag_lt_iff_bit_sub_norm hf₁ hf₂ hZ₁ hZ₂
      have h_bit : b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
                    + b₁.toBitsTriple.significand.toNat
                  < b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
                    + b₂.toBitsTriple.significand.toNat := by
        have h1 : 2 ^ FloatFormat.significandBits
                ≤ b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits := by
          have := Nat.mul_le_mul_right (2 ^ FloatFormat.significandBits) hE₂_pos
          rwa [Nat.one_mul] at this
        rw [hE₁_zero]
        omega
      exact iff_of_true h_lt h_bit
  · have hE₁_pos : 0 < b₁.toBitsTriple.exponent.toNat := by
      rw [Nat.pos_iff_ne_zero]; intro h
      exact hZ₁ (BitVec.eq_of_toNat_eq h)
    by_cases hZ₂ : b₂.toBitsTriple.exponent = 0
    · -- (norm, sub): always FALSE
      have hE₂_zero : b₂.toBitsTriple.exponent.toNat = 0 := by rw [hZ₂]; rfl
      have h_not_lt := not_is_mag_lt_norm_sub hf₁ hf₂ hZ₁ hZ₂
      have h_not_bit : ¬(b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
                          + b₁.toBitsTriple.significand.toNat
                        < b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
                          + b₂.toBitsTriple.significand.toNat) := by
        have h1 : 2 ^ FloatFormat.significandBits
                ≤ b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits := by
          have := Nat.mul_le_mul_right (2 ^ FloatFormat.significandBits) hE₁_pos
          rwa [Nat.one_mul] at this
        rw [hE₂_zero]
        omega
      exact iff_of_false h_not_lt h_not_bit
    · -- (norm, norm): use existing
      have hE₂_pos : 0 < b₂.toBitsTriple.exponent.toNat := by
        rw [Nat.pos_iff_ne_zero]; intro h
        exact hZ₂ (BitVec.eq_of_toNat_eq h)
      have hn₁ : b₁.isNormal :=
        ⟨hZ₁, FloatBits.isFinite_exponent_not_allOnes b₁ hf₁⟩
      have hn₂ : b₂.isNormal :=
        ⟨hZ₂, FloatBits.isFinite_exponent_not_allOnes b₂ hf₂⟩
      have hn₁_val := isNormal_FpSignificand_of_isNormal hn₁
      have hn₂_val := isNormal_FpSignificand_of_isNormal hn₂
      rw [FiniteFp.is_mag_lt_iff_lex_of_normal hn₁_val hn₂_val]
      have he₁ : (⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
            FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).e
          = (b₁.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias :=
        FpExponent_eq_of_normal hn₁
      have he₂ : (⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
            FloatBits.isFinite_validFloatVal hf₂⟩ : FiniteFp).e
          = (b₂.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias :=
        FpExponent_eq_of_normal hn₂
      have hm₁ : (⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
            FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp).m
          = 2 ^ FloatFormat.significandBits + b₁.toBitsTriple.significand.toNat :=
        FpSignificand_eq_of_E_ne_zero hZ₁
      have hm₂ : (⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
            FloatBits.isFinite_validFloatVal hf₂⟩ : FiniteFp).m
          = 2 ^ FloatFormat.significandBits + b₂.toBitsTriple.significand.toNat :=
        FpSignificand_eq_of_E_ne_zero hZ₂
      rw [he₁, he₂, hm₁, hm₂]
      constructor
      · rintro (h | ⟨he, hm⟩)
        · -- ↑E₁ - bias < ↑E₂ - bias → bit comparison
          have hE_lt : b₁.toBitsTriple.exponent.toNat
                     < b₂.toBitsTriple.exponent.toNat := by zify; linarith
          have h1 : (b₁.toBitsTriple.exponent.toNat + 1) * 2 ^ FloatFormat.significandBits
              ≤ b₂.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits :=
            Nat.mul_le_mul_right _ (by omega)
          nlinarith [hT₁_lt, hT₂_lt, h1]
        · -- ↑E₁ - bias = ↑E₂ - bias ∧ p + T₁ < p + T₂ → bit lex
          have hE_eq_nat : b₁.toBitsTriple.exponent.toNat
                         = b₂.toBitsTriple.exponent.toNat := by zify; linarith
          rw [hE_eq_nat]; omega
      · intro h
        by_cases hE_eq : b₁.toBitsTriple.exponent.toNat
                       = b₂.toBitsTriple.exponent.toNat
        · right
          have h_eq_int : (b₁.toBitsTriple.exponent.toNat : ℤ)
                        = b₂.toBitsTriple.exponent.toNat := by exact_mod_cast hE_eq
          refine ⟨by linarith, ?_⟩
          rw [hE_eq] at h
          omega
        · left
          have hE_lt : b₁.toBitsTriple.exponent.toNat
                     < b₂.toBitsTriple.exponent.toNat := by
            by_contra hge
            push_neg at hge
            have hgt : b₂.toBitsTriple.exponent.toNat
                     < b₁.toBitsTriple.exponent.toNat := lt_of_le_of_ne hge (Ne.symm hE_eq)
            have h1 : (b₂.toBitsTriple.exponent.toNat + 1) * 2 ^ FloatFormat.significandBits
                ≤ b₁.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits :=
              Nat.mul_le_mul_right _ (by omega)
            nlinarith [hT₁_lt, hT₂_lt, h1]
          have : (b₁.toBitsTriple.exponent.toNat : ℤ)
                < b₂.toBitsTriple.exponent.toNat := by exact_mod_cast hE_lt
          linarith

/-- **Phase 2 subnormal-tolerant bridge (non-negative).** For two non-negative
finite `FloatBits` (allowing subnormal or normal), IEEE 754 `Fp` ordering on
`ofBits` agrees with unsigned integer comparison on the bit pattern. -/
theorem ofBits_lt_iff_b_toNat_lt_of_finite_nonneg
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hs₁ : b₁.sign = false) (hs₂ : b₂.sign = false) :
    ofBits b₁ < ofBits b₂ ↔ b₁.b.toNat < b₂.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₁⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₂⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_isFinite b₁ hf₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_isFinite b₂ hf₂
  rw [hofb₁, hofb₂]
  show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) ↔ b₁.b.toNat < b₂.b.toNat
  rw [show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) = (f₁ < f₂) from rfl]
  -- Both positive: f₁ < f₂ ↔ is_mag_lt f₁ f₂
  have h_lt_iff : f₁ < f₂ ↔ f₁.is_mag_lt f₂ := by
    rw [FiniteFp.lt_def]
    have h₁ : f₁.s = false := hs₁
    have h₂ : f₂.s = false := hs₂
    simp [h₁, h₂]
  rw [h_lt_iff, is_mag_lt_iff_b_E_T_lt_of_finite b₁ b₂ hf₁ hf₂]
  -- Same sign: both 0#1
  have hsbv : b₁.toBitsTriple.sign = b₂.toBitsTriple.sign := by
    have h1 : b₁.toBitsTriple.sign = 0#1 := by
      unfold FloatBits.sign at hs₁
      rcases BitVec.one_or b₁.toBitsTriple.sign with h | h
      · exact h
      · rw [h] at hs₁; simp at hs₁
    have h2 : b₂.toBitsTriple.sign = 0#1 := by
      unfold FloatBits.sign at hs₂
      rcases BitVec.one_or b₂.toBitsTriple.sign with h | h
      · exact h
      · rw [h] at hs₂; simp at hs₂
    rw [h1, h2]
  rw [FloatBits.b_toNat_lt_iff_of_same_sign b₁ b₂ hsbv]

/-- **Phase 2 subnormal-tolerant bridge (non-positive).** For two non-positive
finite `FloatBits` (subnormal or normal), IEEE 754 `Fp <` is anti-monotone in
unsigned bit comparison — larger magnitude means larger bits but smaller
(more negative) value. -/
theorem ofBits_lt_iff_b_toNat_gt_of_finite_nonpos
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hs₁ : b₁.sign = true) (hs₂ : b₂.sign = true) :
    ofBits b₁ < ofBits b₂ ↔ b₂.b.toNat < b₁.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₁⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₂⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_isFinite b₁ hf₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_isFinite b₂ hf₂
  rw [hofb₁, hofb₂]
  show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) ↔ b₂.b.toNat < b₁.b.toNat
  rw [show Fp.is_total_lt (Fp.finite f₁) (Fp.finite f₂) = (f₁ < f₂) from rfl]
  -- Both negative: f₁ < f₂ ↔ is_mag_lt f₂ f₁ (REVERSED)
  have h_lt_iff : f₁ < f₂ ↔ f₂.is_mag_lt f₁ := by
    rw [FiniteFp.lt_def]
    have h₁ : f₁.s = true := hs₁
    have h₂ : f₂.s = true := hs₂
    simp [h₁, h₂]
  rw [h_lt_iff, is_mag_lt_iff_b_E_T_lt_of_finite b₂ b₁ hf₂ hf₁]
  -- Same sign: both 1#1
  have hsbv : b₂.toBitsTriple.sign = b₁.toBitsTriple.sign := by
    have h1 : b₁.toBitsTriple.sign = 1#1 := by
      unfold FloatBits.sign at hs₁
      rcases BitVec.one_or b₁.toBitsTriple.sign with h | h
      · rw [h] at hs₁; simp at hs₁
      · exact h
    have h2 : b₂.toBitsTriple.sign = 1#1 := by
      unfold FloatBits.sign at hs₂
      rcases BitVec.one_or b₂.toBitsTriple.sign with h | h
      · rw [h] at hs₂; simp at hs₂
      · exact h
    rw [h1, h2]
  rw [FloatBits.b_toNat_lt_iff_of_same_sign b₂ b₁ hsbv]

end SubnormalTolerant

end Fp
