import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Qify

import Flean.Encoding.Util

import Flean.Encoding.Quotient

namespace Fp


-- TODO: We should hopefully be able to use the bitvec representation with the solver integrated into lean, but I need to look into that more.
-- TODO: do we really need to require standard exp range? I think we do for the usual bit saving optimization for finite floats. This isn't major, anyway, since I believe all practical floating point formats are standard.
def toBits [FloatFormat] (f : Fp) : FpQuotient :=
  match f with
  | .finite f =>
    -- We don't need the valid proof to construct the bit pattern, though for reasoning we will need to know it is valid
    let ⟨s, e, m, _valid⟩ := f
    let b := FloatBits.finite s e m
    ⟦b⟧
  | .infinite b =>
    ⟦FloatBits.infinite b⟧
  | .NaN =>
    ⟦FloatBits.NaN false (BitVec.ofNat FloatFormat.significandBits 1) (by
      have := FloatFormat.valid_prec
      unfold FloatFormat.significandBits

      intro h
      rw [BitVec.ofNat_eq_ofNat] at h
      have h := (BitVec.toNat_eq _ _).mp h
      repeat rw [BitVec.toNat_ofNat] at h
      rw [Nat.zero_mod, Nat.one_mod_two_pow] at h
      <;> omega
    )⟧

/-! Convert Bits back into a float.-/
def ofBits [FloatFormat] {st : FloatFormat.isStandardExpRange} (b : FloatBits) : Fp :=
  if hn : b.isNaN then
    .NaN
  else if hi : b.isInfinite then
    .infinite b.sign
  else
    -- let ⟨sign, exponent, significand⟩ := b.toBitsTriple
    -- the above doesn't retain the association between the field and the source function, which means I can't talk about exponent being b's exponent
    let sign := b.toBitsTriple.sign
    let exponent := b.toBitsTriple.exponent
    let significand := b.toBitsTriple.significand

    let sign := sign.toNat == 1
    -- subnormal numbers default to zero, otherwise we subtract the bias
    let is_subnormal := exponent = 0
    let e := if is_subnormal then FloatFormat.min_exp else (exponent.toNat : ℤ) - FloatFormat.exponentBias
    let m := if is_subnormal then significand.toNat else ((BitVec.ofBool true) ++ significand).toNat
    let v : IsValidFiniteVal e m := by
      unfold FloatFormat.isStandardExpRange at st
      unfold IsValidFiniteVal
      have := FloatFormat.valid_exp'_le

      -- == EXPONENT ==
      have e_def : e = (if is_subnormal then FloatFormat.min_exp else (exponent.toNat : ℤ) - FloatFormat.exponentBias) := rfl
      have e_ne_allOnes: exponent ≠ BitVec.allOnes _ := by
        unfold FloatBits.isNaN at hn
        unfold FloatBits.isInfinite at hi
        simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_and, Decidable.not_not, tsub_le_iff_right, e, is_subnormal]
        intro a
        specialize hn a
        specialize hi a
        contradiction

      have exLt := exponent.isLt
      unfold FloatFormat.exponentBits at exLt
      have exLe : ¬is_subnormal → exponent.toNat ≤ 2 ^ (FloatFormat.max_exp.toNat + 1).log2 * 2 - 2 := by
        intro _
        have : exponent.toNat < 2 ^ (FloatFormat.max_exp.toNat + 1).log2 * 2 - 1 := BitVec.ne_allOnes_lt _ e_ne_allOnes
        omega

      -- == SIGNIFICAND ==

      have m_def : m = if is_subnormal then significand.toNat else (BitVec.ofBool true ++ significand).toNat := rfl


      split_ands


      if is_subnormal then
        simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ↓reduceIte, ge_iff_le, le_refl, is_subnormal, e]
      else
        simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ↓reduceIte, ge_iff_le, sub_add_cancel,
          Nat.one_le_cast, is_subnormal, e]
        rename_i h
        have h1 : exponent.toNat ≠ 0 := by
          apply (BitVec.toNat_ne _ 0).mp
          apply h
        omega

      if is_subnormal then
        simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ↓reduceIte, is_subnormal, e]
      else
        simp_all only [tsub_le_iff_right, ite_false]
        unfold FloatFormat.exponentBias
        specialize exLe (by trivial)
        have h1 : 2 ^ (Nat.log2 (FloatFormat.max_exp.toNat + 1)) * 2 ≤ (FloatFormat.max_exp.toNat + 1) * 2 := by
          simp_arith
          rw [Nat.log2_eq_log_two]
          exact Nat.pow_log_le_self 2 (by omega)
        have h3 : 2 ^ (Nat.log2 (FloatFormat.max_exp.toNat + 1)) * 2 - 2 ≤ FloatFormat.max_exp.toNat + FloatFormat.max_exp.toNat := by omega
        apply le_trans
        zify at exLe; exact exLe
        zify at h3; rw [Int.toNat_of_nonneg (by omega)] at h3; exact h3

      have mLt := ((BitVec.ofBool true) ++ significand).isLt
      if is_subnormal then
        rw [m_def]
        simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ne_eq, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
          Nat.ofNat_pos, pow_pos, not_true_eq_false, zero_le, false_implies, e, is_subnormal, exponent, m,
          significand]
        have mLt := significand.isLt
        have := FloatFormat.valid_prec
        unfold FloatFormat.significandBits at mLt
        have : 2 ^ (FloatFormat.prec - 1) ≤ 2 ^ FloatFormat.prec := by
          apply Nat.pow_le_pow_of_le_right
          omega
          omega
        have : 2 ^ (FloatFormat.prec - 1) ≤ 2 ^ FloatFormat.prec - 1 := by
          qify
          rw [Nat.cast_sub, Nat.cast_one, Nat.cast_pow, Nat.cast_two]
          exact (two_pow_pred_lt_two_pow_sub_one FloatFormat.valid_prec).le
          omega
        linarith
      else
        rw [m_def]
        simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ne_eq, ↓reduceIte, not_false_eq_true, true_implies,
          e, is_subnormal, exponent, m, significand]
        unfold FloatFormat.significandBits at mLt
        have := FloatFormat.valid_prec
        simp_rw [show 1 + (FloatFormat.prec - 1) = FloatFormat.prec by omega] at mLt
        omega

      if is_subnormal then
        right
        rw [e_def, m_def]
        split_ands
        · split_ifs
          rfl
        · split_ifs
          have mLt := significand.isLt
          unfold FloatFormat.significandBits at mLt
          omega
      else
        left
        rw [m_def]
        split_ands
        · split_ifs
          have k : ((BitVec.ofBool true) ++ significand).msb = true := by
            unfold BitVec.msb BitVec.getMsb
            simp only [add_pos_iff, zero_lt_one, tsub_pos_iff_lt, true_or, decide_True,
              BitVec.ofBool_true, BitVec.ofNat_eq_ofNat, add_tsub_cancel_left, tsub_zero,
              BitVec.getLsb_append, lt_self_iff_false, decide_False, le_refl, BitVec.getLsb_ge,
              tsub_eq_zero_of_le, BitVec.getLsb_one, Bool.and_self, cond_false]
          have j := BitVec.toNat_ge_of_msb_true k
          simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ne_eq, BitVec.ofBool_true, BitVec.toNat_append,
            BitVec.toNat_ofNat, pow_one, Nat.mod_succ, add_tsub_cancel_left, ge_iff_le, e, is_subnormal, exponent, m,
            significand]
        · split_ifs
          have := FloatFormat.valid_prec
          have mLt := ((BitVec.ofBool true) ++ significand).isLt
          unfold FloatFormat.significandBits at mLt
          simp_rw [show 1 + (FloatFormat.prec - 1) = FloatFormat.prec by omega] at mLt
          omega
    .finite ⟨sign, e, m, v⟩


end Fp

def f := @FiniteFp.toRat FloatFormat.Binary32
#eval! f (0 : @FiniteFp FloatFormat.Binary32)
def f' := @Fp.toBits FloatFormat.Binary32
def v := f' (0 : @Fp FloatFormat.Binary32)
-- #eval! @Fp.FpQuotient.representative FloatFormat.Binary32 v FloatFormat.binary32_standard_exp_range
-- #eval! (@toBits FloatFormat.Binary32 (0 : @Fp FloatFormat.Binary32) FloatFormat.binary32_standard_exp_range).representative
