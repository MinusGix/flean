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

/-- For bit-normal `b`, `FpSignificand = 2^sigBits + T.toNat`. -/
private theorem FpSignificand_eq_of_normal [FloatFormat] {b : FloatBits}
    (hn : b.isNormal) :
    b.FpSignificand
      = 2 ^ FloatFormat.significandBits + b.toBitsTriple.significand.toNat := by
  rw [FloatBits.FpSignificand_def, if_neg hn.1]
  have hT_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b.toBitsTriple.significand.isLt
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hT_lt, Nat.shiftLeft_eq]
  show (BitVec.ofBool true).toNat * 2 ^ FloatFormat.significandBits
      + b.toBitsTriple.significand.toNat = _
  simp

/-- Decoding `b : FloatBits` to its `Fp.finite` form for a bit-normal `b`. -/
private theorem ofBits_eq_finite_of_normal [StdFloatFormat] (b : FloatBits)
    (hn : b.isNormal) :
    ofBits b = Fp.finite ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal
        (FloatBits.notNaN_notInfinite b
          (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))⟩ := by
  have hni : ¬b.isNaN := fun ⟨h, _⟩ => hn.2 h
  have hii : ¬b.isInfinite := fun ⟨h, _⟩ => hn.2 h
  have hf : b.isFinite := FloatBits.notNaN_notInfinite b hni hii
  have h_step : ofBits b = Fp.finite ⟨b.toBitsTriple.sign.toNat == 1,
      b.FpExponent, b.FpSignificand, FloatBits.isFinite_validFloatVal hf⟩ := by
    unfold ofBits; rw [dif_neg hni, dif_neg hii]
  rw [h_step]
  congr 1; apply (FiniteFp.eq_def _ _).mpr
  refine ⟨?_, rfl, rfl⟩
  show (b.toBitsTriple.sign.toNat == 1) = b.sign
  unfold FloatBits.sign
  rcases BitVec.one_or b.toBitsTriple.sign with h | h <;> rw [h] <;> rfl

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

end Fp
