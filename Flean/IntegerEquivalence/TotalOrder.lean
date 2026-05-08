import Flean.IntegerEquivalence.Compare

/-! # FP ↔ Integer equivalence: total ordering ↔ signed-magnitude bit comparison

Phase 2.5 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

IEEE 754 §5.10 `totalOrder` imposes a total ordering on FP values that
matches signed-magnitude integer comparison on the bit pattern. This file
proves that bridge for non-NaN inputs (covers finites — extension to
infinities is mechanical given the existing Phase 2 sub-tolerant work).

## Why "signed-magnitude" and not just "signed integer"?

Naive interpretation: view the bit pattern as a signed integer (sign bit + the
rest as magnitude with a sign). The catch: `-0` has bit pattern
`1₍ₛ₎ ++ 0` (magnitude zero), so as an integer it'd be `-0 = 0`, which would
make `-0 = +0`. But the IEEE total order *does* distinguish: `-0 < +0`.

The correct signed-magnitude comparison: lex on `(sign, magnitude)` where
positives are ordered by ascending magnitude and negatives by descending
magnitude (more negative ⇒ smaller). The negative-vs-positive case is
decided by sign alone — even when both have magnitude zero.

In hardware this is implemented as a "twos-complement adjustment": flip all
bits except sign for negatives, then compare as signed int. We use the
sign + `b.b.toNat` formulation (the natural Lean encoding) instead.
-/

namespace Fp

/-- IEEE 754 totalOrder bit comparison on `FloatBits`: lex on `(sign, |bits|)`
with positives ascending and negatives descending in magnitude. Crucially,
negatives are *strictly less* than positives even at magnitude zero, so
`-0 < +0`. -/
def totalOrderBitLt [FloatFormat] (b₁ b₂ : FloatBits) : Prop :=
  (b₁.sign ∧ ¬b₂.sign) ∨
  (b₁.sign ∧ b₂.sign ∧ b₂.b.toNat < b₁.b.toNat) ∨
  (¬b₁.sign ∧ ¬b₂.sign ∧ b₁.b.toNat < b₂.b.toNat)

/-- **Phase 2.5 bridge.** For two finite (non-NaN, non-infinite) `FloatBits`,
IEEE 754 totalOrder on `ofBits` agrees with signed-magnitude bit comparison.

The cross-sign cases are decided by sign alone (positive > negative always,
including the `-0 < +0` corner). The same-sign cases reduce to the existing
Phase 2 sub-tolerant bridges. -/
theorem ofBits_lt_iff_totalOrderBitLt_of_finite [StdFloatFormat]
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite) :
    ofBits b₁ < ofBits b₂ ↔ totalOrderBitLt b₁ b₂ := by
  unfold totalOrderBitLt
  by_cases hs₁ : b₁.sign
  · by_cases hs₂ : b₂.sign
    · -- (true, true): both negative, use sub-tolerant nonpos (anti-monotone)
      rw [ofBits_lt_iff_b_toNat_gt_of_finite_nonpos b₁ b₂ hf₁ hf₂ hs₁ hs₂]
      simp [hs₁, hs₂]
    · -- (true, false): negative < positive, both LHS and RHS true
      have hLHS : ofBits b₁ < ofBits b₂ := by
        have hofb₁ : ofBits b₁ = Fp.finite ⟨b₁.sign, b₁.FpExponent,
            b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ :=
          ofBits_eq_finite_of_isFinite b₁ hf₁
        have hofb₂ : ofBits b₂ = Fp.finite ⟨b₂.sign, b₂.FpExponent,
            b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩ :=
          ofBits_eq_finite_of_isFinite b₂ hf₂
        rw [hofb₁, hofb₂]
        show Fp.is_total_lt (Fp.finite _) (Fp.finite _)
        show ((⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
                FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp)
              < ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
                FloatBits.isFinite_validFloatVal hf₂⟩)
        rw [FiniteFp.lt_def]
        simp [hs₁, hs₂]
      exact iff_of_true hLHS (Or.inl ⟨hs₁, hs₂⟩)
  · by_cases hs₂ : b₂.sign
    · -- (false, true): positive > negative, both LHS and RHS false
      have hLHS_false : ¬(ofBits b₁ < ofBits b₂) := by
        have hofb₁ : ofBits b₁ = Fp.finite ⟨b₁.sign, b₁.FpExponent,
            b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ :=
          ofBits_eq_finite_of_isFinite b₁ hf₁
        have hofb₂ : ofBits b₂ = Fp.finite ⟨b₂.sign, b₂.FpExponent,
            b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩ :=
          ofBits_eq_finite_of_isFinite b₂ hf₂
        rw [hofb₁, hofb₂]
        show ¬Fp.is_total_lt (Fp.finite _) (Fp.finite _)
        show ¬((⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
                FloatBits.isFinite_validFloatVal hf₁⟩ : FiniteFp)
              < ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
                FloatBits.isFinite_validFloatVal hf₂⟩)
        rw [FiniteFp.lt_def]
        simp [hs₁, hs₂]
      have hRHS_false : ¬totalOrderBitLt b₁ b₂ := by
        unfold totalOrderBitLt
        rintro (⟨h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩) <;> simp_all
      exact iff_of_false hLHS_false hRHS_false
    · -- (false, false): both non-negative, use sub-tolerant nonneg
      have hs₁_eq : b₁.sign = false := by cases h : b₁.sign <;> simp_all
      have hs₂_eq : b₂.sign = false := by cases h : b₂.sign <;> simp_all
      rw [ofBits_lt_iff_b_toNat_lt_of_finite_nonneg b₁ b₂ hf₁ hf₂ hs₁_eq hs₂_eq]
      simp [hs₁, hs₂]

/-! ## Extension to ±∞

The `totalOrderBitLt` formula extends mechanically to ±∞ inputs: the sign
bit decides cross-sign, and ±∞ has the maximum bit-magnitude in its sign
class, so any finite of the same sign has strictly smaller bit-magnitude.
This means same-sign comparisons against ±∞ work out via the "negative
in same sign class is smaller" or "positive in same sign class is smaller"
ordering. -/

namespace FloatBits

variable [FloatFormat]

/-- For `b.sign = false`, the underlying sign-BitVec has `.toNat = 0`. -/
private theorem sign_toNat_zero_of_sign_false (b : FloatBits) (hs : b.sign = false) :
    b.toBitsTriple.sign.toNat = 0 := by
  unfold FloatBits.sign at hs
  have h_lt : b.toBitsTriple.sign.toNat < 2 := by
    have := b.toBitsTriple.sign.isLt; simpa using this
  by_contra h_ne
  have h_one_nat : b.toBitsTriple.sign.toNat = 1 := by omega
  have h_eq_one : b.toBitsTriple.sign = 1 := by
    apply BitVec.eq_of_toNat_eq; rw [h_one_nat]; rfl
  rw [h_eq_one] at hs
  simp at hs

/-- For `b.sign = true`, the underlying sign-BitVec has `.toNat = 1`. -/
private theorem sign_toNat_one_of_sign_true (b : FloatBits) (hs : b.sign = true) :
    b.toBitsTriple.sign.toNat = 1 := by
  unfold FloatBits.sign at hs
  have h_lt : b.toBitsTriple.sign.toNat < 2 := by
    have := b.toBitsTriple.sign.isLt; simpa using this
  by_contra h_ne
  have h_zero_nat : b.toBitsTriple.sign.toNat = 0 := by omega
  have h_eq_zero : b.toBitsTriple.sign = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [h_zero_nat]; rfl
  rw [h_eq_zero] at hs
  simp at hs

/-- Sign components of two FloatBits with the same `.sign` (Bool) have
equal `toNat` (the 1-bit BitVec is determined by the Bool). -/
private theorem sign_bv_toNat_eq_of_same_sign (b₁ b₂ : FloatBits)
    (hs : b₁.sign = b₂.sign) :
    b₁.toBitsTriple.sign.toNat = b₂.toBitsTriple.sign.toNat := by
  by_cases h : b₁.sign
  · have h₂ : b₂.sign = true := by rw [← hs]; exact h
    rw [sign_toNat_one_of_sign_true b₁ h, sign_toNat_one_of_sign_true b₂ h₂]
  · rw [Bool.not_eq_true] at h
    have h₂ : b₂.sign = false := by rw [← hs]; exact h
    rw [sign_toNat_zero_of_sign_false b₁ h, sign_toNat_zero_of_sign_false b₂ h₂]

/-- For finite `b`, the bit-magnitude `b.b.toNat` strictly less than that of
`±∞` of the same sign. Used to extend `totalOrderBitLt` to allow ±∞ inputs. -/
private theorem finite_b_toNat_lt_inf_of_same_sign
    (b binf : FloatBits) (hf : b.isFinite) (hi : binf.isInfinite)
    (hs : b.sign = binf.sign) :
    b.b.toNat < binf.b.toNat := by
  rw [FloatBits.b_toNat_eq_triple b, FloatBits.b_toNat_eq_triple binf]
  have hE_inf : binf.toBitsTriple.exponent.toNat = 2 ^ FloatFormat.exponentBits - 1 := by
    have := hi.1
    unfold FloatBits.isExponentAllOnes at this
    rw [this, BitVec.toNat_allOnes]
  have hT_inf : binf.toBitsTriple.significand.toNat = 0 := by
    have := hi.2
    unfold FloatBits.isTSignificandZero at this
    rw [this]; simp
  have hs_eq : b.toBitsTriple.sign.toNat = binf.toBitsTriple.sign.toNat :=
    sign_bv_toNat_eq_of_same_sign b binf hs
  rw [hE_inf, hT_inf, hs_eq]
  -- Bit magnitudes: finite has E < 2^expBits - 1.
  have hE_b_lt : b.toBitsTriple.exponent.toNat ≤ 2 ^ FloatFormat.exponentBits - 2 := by
    -- ¬b.isExponentAllOnes (else b not finite).
    have h_not_all : ¬b.isExponentAllOnes := by
      intro h
      apply hf.2  -- ¬b.isInfinite
      refine ⟨h, ?_⟩
      -- T must be 0 to be ∞. Actually wait — if E = allOnes ∧ T ≠ 0 ⇒ NaN, ∧ T = 0 ⇒ ∞.
      -- We have ¬isFinite if either NaN or ∞, so finite means E ≠ allOnes (regardless of T)
      -- OR (E = allOnes ∧ T = 0 fails — but ∞ has T = 0, contradicts ¬∞).
      -- The cleanest: if E = allOnes and we want ¬finite, then b is either NaN or ∞.
      -- If T = 0, ∞; if T ≠ 0, NaN. Either way, b not finite.
      by_cases hT : b.isTSignificandZero
      · exact hT
      · exfalso; exact hf.1 ⟨h, hT⟩
    unfold FloatBits.isExponentAllOnes at h_not_all
    have h_lt : b.toBitsTriple.exponent.toNat < 2 ^ FloatFormat.exponentBits :=
      b.toBitsTriple.exponent.isLt
    -- E.toNat ≠ allOnes.toNat = 2^expBits - 1 ⇒ E.toNat < 2^expBits - 1 ⇒ ≤ 2^expBits - 2.
    have h_ne : b.toBitsTriple.exponent.toNat ≠ 2 ^ FloatFormat.exponentBits - 1 := by
      intro h_eq
      apply h_not_all
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_allOnes]; exact h_eq
    omega
  have hT_b_lt : b.toBitsTriple.significand.toNat < 2 ^ FloatFormat.significandBits :=
    b.toBitsTriple.significand.isLt
  -- Goal: S + Eb·2^sb + Tb < S + (2^expBits - 1)·2^sb + 0
  -- Equivalent: Eb·2^sb + Tb < (2^expBits - 1)·2^sb.
  -- Use Eb ≤ 2^expBits - 2 ⇒ Eb·2^sb ≤ (2^expBits - 2)·2^sb.
  -- And Tb < 2^sb. So Eb·2^sb + Tb ≤ (2^expBits - 2)·2^sb + (2^sb - 1)
  --                              < (2^expBits - 1)·2^sb.
  have hEB_pos : 0 < (2 : ℕ) ^ FloatFormat.exponentBits := Nat.two_pow_pos _
  have hEB_ge_2 : 2 ≤ (2 : ℕ) ^ FloatFormat.exponentBits := by
    have hep := FloatFormat.exponentBits_pos
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^FloatFormat.exponentBits := Nat.pow_le_pow_right (by norm_num) hep
  have hSB_pos : 0 < (2 : ℕ) ^ FloatFormat.significandBits := Nat.two_pow_pos _
  have h_eb_mul : b.toBitsTriple.exponent.toNat * 2 ^ FloatFormat.significandBits
                ≤ (2 ^ FloatFormat.exponentBits - 2) * 2 ^ FloatFormat.significandBits :=
    Nat.mul_le_mul_right _ hE_b_lt
  have h_expand :
      (2 ^ FloatFormat.exponentBits - 1) * 2 ^ FloatFormat.significandBits
        = (2 ^ FloatFormat.exponentBits - 2) * 2 ^ FloatFormat.significandBits
            + 2 ^ FloatFormat.significandBits := by
    have heq : 2 ^ FloatFormat.exponentBits - 1
              = (2 ^ FloatFormat.exponentBits - 2) + 1 := by omega
    rw [heq]; ring
  omega

end FloatBits

/-- **Phase 2.5 bridge (extended).** For two non-NaN `FloatBits` (finite or
±∞), IEEE 754 totalOrder on `ofBits` agrees with signed-magnitude bit
comparison. ±∞ have maximal bit-magnitude in their sign class, so the
`totalOrderBitLt` formula handles them uniformly. -/
theorem ofBits_lt_iff_totalOrderBitLt_of_non_nan [StdFloatFormat]
    (b₁ b₂ : FloatBits) (hn₁ : ¬b₁.isNaN) (hn₂ : ¬b₂.isNaN) :
    ofBits b₁ < ofBits b₂ ↔ totalOrderBitLt b₁ b₂ := by
  by_cases hi₁ : b₁.isInfinite
  · by_cases hi₂ : b₂.isInfinite
    · -- Both ±∞.
      -- ofBits b = Fp.infinite b.sign.
      have hofb₁ : ofBits b₁ = Fp.infinite b₁.sign := by
        unfold ofBits; rw [dif_neg hn₁, dif_pos hi₁]
      have hofb₂ : ofBits b₂ = Fp.infinite b₂.sign := by
        unfold ofBits; rw [dif_neg hn₂, dif_pos hi₂]
      rw [hofb₁, hofb₂]
      unfold totalOrderBitLt
      -- Both sides reduce to sign analysis. Same-sign infs have same b.b.toNat.
      have hb_eq_of_same_sign :
          b₁.sign = b₂.sign → b₁.b.toNat = b₂.b.toNat := by
        intro hs
        rw [FloatBits.b_toNat_eq_triple b₁, FloatBits.b_toNat_eq_triple b₂]
        -- All three components equal: sign (from hs), E (both allOnes), T (both 0).
        have hE₁ : b₁.toBitsTriple.exponent.toNat = 2 ^ FloatFormat.exponentBits - 1 := by
          have := hi₁.1
          unfold FloatBits.isExponentAllOnes at this
          rw [this, BitVec.toNat_allOnes]
        have hE₂ : b₂.toBitsTriple.exponent.toNat = 2 ^ FloatFormat.exponentBits - 1 := by
          have := hi₂.1
          unfold FloatBits.isExponentAllOnes at this
          rw [this, BitVec.toNat_allOnes]
        have hT₁ : b₁.toBitsTriple.significand.toNat = 0 := by
          have := hi₁.2
          unfold FloatBits.isTSignificandZero at this
          rw [this]; simp
        have hT₂ : b₂.toBitsTriple.significand.toNat = 0 := by
          have := hi₂.2
          unfold FloatBits.isTSignificandZero at this
          rw [this]; simp
        have hs_eq : b₁.toBitsTriple.sign.toNat = b₂.toBitsTriple.sign.toNat :=
          FloatBits.sign_bv_toNat_eq_of_same_sign b₁ b₂ hs
        rw [hs_eq, hE₁, hE₂, hT₁, hT₂]
      by_cases hs₁ : b₁.sign
      · by_cases hs₂ : b₂.sign
        · -- (true, true): -∞ < -∞ false; bit-wise also false (same b.b.toNat).
          have hb_eq : b₁.b.toNat = b₂.b.toNat := hb_eq_of_same_sign (by rw [hs₁, hs₂])
          constructor
          · intro h
            simp [Fp.is_total_lt, hs₁, hs₂] at h
          · rintro (⟨_, hh⟩ | ⟨_, _, hh⟩ | ⟨hh, _⟩)
            · exact absurd hs₂ hh
            · linarith [hb_eq]
            · exact absurd hs₁ hh
        · -- (true, false): -∞ < +∞ true, RHS first disjunct true.
          have hs₂_eq : b₂.sign = false := by rw [Bool.not_eq_true] at hs₂; exact hs₂
          have hLHS : Fp.infinite b₁.sign < Fp.infinite b₂.sign := by
            rw [hs₁, hs₂_eq]
            show Fp.is_total_lt (Fp.infinite true) (Fp.infinite false)
            rfl
          exact iff_of_true hLHS (Or.inl ⟨hs₁, by simp [hs₂_eq]⟩)
      · by_cases hs₂ : b₂.sign
        · -- (false, true): +∞ ≮ -∞, RHS false.
          have hLHS : ¬(Fp.infinite b₁.sign < Fp.infinite b₂.sign) := by
            rw [Bool.not_eq_true] at hs₁
            rw [hs₁, hs₂]
            intro h
            simp [Fp.is_total_lt] at h
          have hRHS : ¬totalOrderBitLt b₁ b₂ := by
            unfold totalOrderBitLt
            rintro (⟨h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩) <;> simp_all
          exact iff_of_false hLHS hRHS
        · -- (false, false): +∞ < +∞ false; bit-wise false (same b.b.toNat).
          have hb_eq : b₁.b.toNat = b₂.b.toNat := hb_eq_of_same_sign (by
            rw [Bool.not_eq_true] at hs₁ hs₂; rw [hs₁, hs₂])
          constructor
          · intro h
            rw [Bool.not_eq_true] at hs₁ hs₂
            rw [hs₁, hs₂] at h
            simp [Fp.is_total_lt] at h
          · rintro (⟨hh, _⟩ | ⟨hh, _, _⟩ | ⟨_, _, hh⟩)
            · exact absurd hh hs₁
            · exact absurd hh hs₁
            · linarith [hb_eq]
    · -- b₁ ∞, b₂ finite.
      have hf₂ : b₂.isFinite := ⟨hn₂, hi₂⟩
      have hofb₁ : ofBits b₁ = Fp.infinite b₁.sign := by
        unfold ofBits; rw [dif_neg hn₁, dif_pos hi₁]
      rw [hofb₁]
      rw [ofBits_eq_finite_of_isFinite b₂ hf₂]
      by_cases hs₁ : b₁.sign
      · by_cases hs₂ : b₂.sign
        · -- (true neg-∞, true neg-fin): -∞ < neg-fin true.
          have hLHS : Fp.infinite b₁.sign < Fp.finite ⟨b₂.sign, b₂.FpExponent,
              b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩ := by
            rw [hs₁]; show Fp.is_total_lt (Fp.infinite true) (Fp.finite _); rfl
          -- RHS: second disjunct (b₁.sign true, b₂.sign true, b₂.b.toNat < b₁.b.toNat).
          have hRHS : totalOrderBitLt b₁ b₂ := by
            right; left; refine ⟨hs₁, hs₂, ?_⟩
            exact FloatBits.finite_b_toNat_lt_inf_of_same_sign b₂ b₁ hf₂ hi₁ (by rw [hs₁, hs₂])
          exact iff_of_true hLHS hRHS
        · -- (true neg-∞, false pos-fin): -∞ < pos-fin true. RHS first disjunct.
          have hLHS : Fp.infinite b₁.sign < Fp.finite ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩ := by
            rw [hs₁]; show Fp.is_total_lt (Fp.infinite true) (Fp.finite _); rfl
          exact iff_of_true hLHS (Or.inl ⟨hs₁, by simp [hs₂]⟩)
      · -- b₁ = +∞.
        rw [Bool.not_eq_true] at hs₁
        by_cases hs₂ : b₂.sign
        · -- (+∞, neg-fin): +∞ ≮ neg-fin. RHS no disjunct.
          have hLHS : ¬(Fp.infinite b₁.sign < Fp.finite ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩) := by
            rw [hs₁]; intro h
            simp [Fp.is_total_lt] at h
          have hRHS : ¬totalOrderBitLt b₁ b₂ := by
            unfold totalOrderBitLt
            rintro (⟨h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩) <;> simp_all
          exact iff_of_false hLHS hRHS
        · -- (+∞, pos-fin): +∞ ≮ pos-fin. RHS third disjunct: needs b₁.b.toNat < b₂.b.toNat (false).
          rw [Bool.not_eq_true] at hs₂
          have hLHS : ¬(Fp.infinite b₁.sign < Fp.finite ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand, FloatBits.isFinite_validFloatVal hf₂⟩) := by
            rw [hs₁]; intro h
            simp [Fp.is_total_lt] at h
          have hb_lt : b₂.b.toNat < b₁.b.toNat :=
            FloatBits.finite_b_toNat_lt_inf_of_same_sign b₂ b₁ hf₂ hi₁ (by rw [hs₁, hs₂])
          have hRHS : ¬totalOrderBitLt b₁ b₂ := by
            unfold totalOrderBitLt
            rintro (⟨hh, _⟩ | ⟨hh, _, _⟩ | ⟨_, _, hh⟩) <;> simp_all
            · linarith
          exact iff_of_false hLHS hRHS
  · by_cases hi₂ : b₂.isInfinite
    · -- b₁ finite, b₂ ∞.
      have hf₁ : b₁.isFinite := ⟨hn₁, hi₁⟩
      have hofb₂ : ofBits b₂ = Fp.infinite b₂.sign := by
        unfold ofBits; rw [dif_neg hn₂, dif_pos hi₂]
      rw [hofb₂]
      rw [ofBits_eq_finite_of_isFinite b₁ hf₁]
      by_cases hs₁ : b₁.sign
      · by_cases hs₂ : b₂.sign
        · -- (neg-fin, -∞): neg-fin ≮ -∞. RHS second disjunct false: needs b₂.b.toNat < b₁.b.toNat.
          have hLHS : ¬(Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ < Fp.infinite b₂.sign) := by
            rw [hs₂]; intro h
            simp [Fp.is_total_lt] at h
          have hb_lt : b₁.b.toNat < b₂.b.toNat :=
            FloatBits.finite_b_toNat_lt_inf_of_same_sign b₁ b₂ hf₁ hi₂ (by rw [hs₁, hs₂])
          have hRHS : ¬totalOrderBitLt b₁ b₂ := by
            unfold totalOrderBitLt
            rintro (⟨_, hh⟩ | ⟨_, _, hh⟩ | ⟨hh, _⟩) <;> simp_all
            · linarith
          exact iff_of_false hLHS hRHS
        · -- (neg-fin, +∞): neg-fin < +∞. RHS first disjunct.
          rw [Bool.not_eq_true] at hs₂
          have hLHS : Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ < Fp.infinite b₂.sign := by
            rw [hs₂]; show Fp.is_total_lt (Fp.finite _) (Fp.infinite false); rfl
          exact iff_of_true hLHS (Or.inl ⟨hs₁, by simp [hs₂]⟩)
      · -- b₁ pos-fin.
        rw [Bool.not_eq_true] at hs₁
        by_cases hs₂ : b₂.sign
        · -- (pos-fin, -∞): pos-fin ≮ -∞. RHS no disjunct.
          have hLHS : ¬(Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ < Fp.infinite b₂.sign) := by
            rw [hs₂]; intro h
            simp [Fp.is_total_lt] at h
          have hRHS : ¬totalOrderBitLt b₁ b₂ := by
            unfold totalOrderBitLt
            rintro (⟨h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩) <;> simp_all
          exact iff_of_false hLHS hRHS
        · -- (pos-fin, +∞): pos-fin < +∞. RHS third disjunct.
          rw [Bool.not_eq_true] at hs₂
          have hLHS : Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand, FloatBits.isFinite_validFloatVal hf₁⟩ < Fp.infinite b₂.sign := by
            rw [hs₂]; show Fp.is_total_lt (Fp.finite _) (Fp.infinite false); rfl
          have hb_lt : b₁.b.toNat < b₂.b.toNat :=
            FloatBits.finite_b_toNat_lt_inf_of_same_sign b₁ b₂ hf₁ hi₂ (by rw [hs₁, hs₂])
          have hns₁ : ¬b₁.sign = true := by rw [hs₁]; simp
          have hns₂ : ¬b₂.sign = true := by rw [hs₂]; simp
          exact iff_of_true hLHS (Or.inr (Or.inr ⟨hns₁, hns₂, hb_lt⟩))
    · -- both finite.
      have hf₁ : b₁.isFinite := ⟨hn₁, hi₁⟩
      have hf₂ : b₂.isFinite := ⟨hn₂, hi₂⟩
      exact ofBits_lt_iff_totalOrderBitLt_of_finite b₁ b₂ hf₁ hf₂

end Fp
