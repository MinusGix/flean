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

end Fp
