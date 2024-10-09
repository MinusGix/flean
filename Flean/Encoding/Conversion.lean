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
    let ⟨s, e, m, valid⟩ := f
    let b := FloatBits.finite s e m valid
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

@[reducible]
def FloatBits.FpExponent [FloatFormat] (b : FloatBits) : ℤ := if b.toBitsTriple.exponent = 0 then FloatFormat.min_exp else (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias

def FloatBits.FpExponent_def [FloatFormat] (b : FloatBits) : b.FpExponent = if b.toBitsTriple.exponent = 0 then FloatFormat.min_exp else (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := rfl

/-- The Integral Significand. Attach the leading 1 to normal numbers; This is technically only valid for the standard emax/emin range. -/
@[reducible]
def FloatBits.FpSignificand [FloatFormat] (b : FloatBits) : ℕ := if b.toBitsTriple.exponent = 0 then b.toBitsTriple.significand.toNat else ((BitVec.ofBool true) ++ b.toBitsTriple.significand).toNat

def FloatBits.FpSignificand_def [FloatFormat] (b : FloatBits) : b.FpSignificand = if b.toBitsTriple.exponent = 0 then b.toBitsTriple.significand.toNat else ((BitVec.ofBool true) ++ b.toBitsTriple.significand).toNat := rfl

theorem FloatBits.isFinite_validFloatVal [StdFloatFormat] {b : FloatBits} (hf : b.isFinite) : IsValidFiniteVal b.FpExponent b.FpSignificand := by
  let exponent := b.toBitsTriple.exponent
  let significand := b.toBitsTriple.significand

  let is_subnormal := exponent = 0
  let e := b.FpExponent
  let m := b.FpSignificand
  have st := StdFloatFormat.st
  unfold FloatFormat.isStandardExpRange at st
  unfold IsValidFiniteVal
  have := FloatFormat.exp_order_le

  -- == EXPONENT ==
  have e_ne_allOnes: exponent ≠ BitVec.allOnes _ := FloatBits.isFinite_exponent_not_allOnes b hf

  have exLt := exponent.isLt
  unfold FloatFormat.exponentBits at exLt
  have exLe : ¬is_subnormal → exponent.toNat ≤ 2 ^ (Nat.clog 2 (FloatFormat.max_exp.toNat + 1)) * 2 - 2 := by
    intro _
    have : exponent.toNat < 2 ^ (Nat.clog 2 (FloatFormat.max_exp.toNat + 1)) * 2 - 1 := BitVec.ne_allOnes_lt _ e_ne_allOnes
    omega

  -- For some reason after adding these, rather than using an `e = if ...` definition, split_ifs stopped automatically getting rid of contradicting paths
  unfold FloatBits.FpExponent FloatBits.FpSignificand
  refold_let exponent
  refold_let significand

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

  if hs : is_subnormal then
    simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ↓reduceIte, is_subnormal, e]
  else
    split_ifs; contradiction
    rw [tsub_le_iff_right]
    unfold FloatFormat.exponentBias
    specialize exLe (by trivial)
    have := (Nat.le_pow_iff_clog_le ?_).mp exLt.le
    have a0 : FloatFormat.max_exp.toNat + 1 ≤ 2^FloatFormat.exponentBits2 := Nat.le_pow_clog (by norm_num) _
    have a2 : exponent.toNat + 1 < 2^FloatFormat.exponentBits := by
      unfold FloatFormat.exponentBits
      omega
    have a5 : 2 * FloatFormat.max_exp.toNat + 2 ≤ 2 * 2^FloatFormat.exponentBits2 := by omega
    simp_rw [StdFloatFormat.exponentBits_def] at a2
    have a7 : 2 * FloatFormat.max_exp + 2 ≤ 2^FloatFormat.exponentBits := by
      unfold FloatFormat.exponentBits
      unfold FloatFormat.exponentBits2 at a5
      conv at a5 => rhs; rw [mul_comm]; rhs; rw [← pow_one 2]
      rw [← pow_add] at a5
      zify at a5
      rw [Int.toNat_of_nonneg (by omega)] at a5
      exact a5
    simp_rw [StdFloatFormat.exponentBits_def] at a7
    rw [StdFloatFormat.max_exp_def]
    rw [show (2 : ℤ) ^ StdFloatFormat.exp_pow - 1 + (2 ^ StdFloatFormat.exp_pow - 1) = 2 ^ (StdFloatFormat.exp_pow + 1) - 2 by omega]
    have : (exponent.toNat : ℤ) < 2 ^ (StdFloatFormat.exp_pow + 1) - 1 := by linarith
    omega
    norm_num

  have mLt := ((BitVec.ofBool true) ++ significand).isLt
  if is_subnormal then
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
    simp_all only [tsub_le_iff_right, BitVec.ofNat_eq_ofNat, ne_eq, ↓reduceIte, not_false_eq_true, true_implies,
      e, is_subnormal, exponent, m, significand]
    unfold FloatFormat.significandBits at mLt
    have := FloatFormat.valid_prec
    simp_rw [show 1 + (FloatFormat.prec - 1) = FloatFormat.prec by omega] at mLt
    omega

  if is_subnormal then
    right
    split_ands
    · split_ifs
      <;> rfl
    · split_ifs
      have mLt := significand.isLt
      unfold FloatFormat.significandBits at mLt
      omega
      contradiction
  else
    left
    split_ands
    · split_ifs; contradiction
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
    · split_ifs; contradiction
      have := FloatFormat.valid_prec
      have mLt := ((BitVec.ofBool true) ++ significand).isLt
      unfold FloatFormat.significandBits at mLt
      simp_rw [show 1 + (FloatFormat.prec - 1) = FloatFormat.prec by omega] at mLt
      omega

/-! Convert Bits back into a float.-/
def ofBits [StdFloatFormat] (b : FloatBits) : Fp :=
  if hn : b.isNaN then
    .NaN
  else if hi : b.isInfinite then
    .infinite b.sign
  else
    let hf : b.isFinite := FloatBits.notNaN_notInfinite b hn hi

    .finite ⟨b.toBitsTriple.sign.toNat == 1, b.FpExponent, b.FpSignificand, FloatBits.isFinite_validFloatVal hf⟩

theorem lift_isNaN [FloatFormat] {f : Fp} (h : f.isNaN) : (toBits f).isNaN := by
  unfold Fp.isNaN at h
  unfold toBits FpQuotient.isNaN FloatBits.isNaN
  subst h
  simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, Quotient.lift_mk]
  apply And.intro
  · unfold FloatBits.NaN FloatBits.isExponentAllOnes
    norm_num
    rw [FloatBits.construct_exponent_eq_BitsTriple]
  · apply Aesop.BuiltinRules.not_intro
    intro a
    unfold FloatBits.NaN at a
    rw [FloatBits.construct_significand_eq_BitsTriple] at a
    have := FloatFormat.significandBits_pos
    have a := (BitVec.toNat_eq _ _).mp a
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.one_mod_of_ne_one, Nat.zero_mod] at a
    contradiction
    simp_all only [gt_iff_lt, tsub_pos_iff_lt, Nat.one_mod_two_pow, Nat.zero_mod, one_ne_zero]

theorem lift_isInfinite [FloatFormat] {f : Fp} (h : f.isInfinite) : (toBits f).isInfinite := by
  unfold Fp.isInfinite at h
  unfold toBits FpQuotient.isInfinite FloatBits.isInfinite
  cases h
  all_goals {
    rename_i h;
    subst h
    simp only [Quotient.lift_mk]
    unfold FloatBits.infinite FloatBits.isExponentAllOnes FloatBits.isTSignificandZero
    rw [FloatBits.construct_exponent_eq_BitsTriple, FloatBits.construct_significand_eq_BitsTriple]
    trivial
  }

theorem lift_isFinite [FloatFormat] {f : Fp} (st : FloatFormat.isStandardExpRange) (h : f.isFinite) : (toBits f).isFinite := by
  unfold Fp.isFinite at h
  rw [Bool.false_eq_true] at h
  split at h
  rename_i x
  unfold toBits FpQuotient.isFinite FloatBits.isFinite
  rw [@Quotient.liftOn_mk]
  exact FloatBits.finite_isFinite x.s x.e x.m st x.valid
  all_goals contradiction

theorem ofBits_zero [StdFloatFormat] : @ofBits _ 0 = 0 := by
  unfold ofBits
  split_ifs with h1 h2
  · unfold FloatBits.isNaN FloatBits.isExponentAllOnes at h1
    rw [FloatBits.zero_def', FloatBits.construct_exponent_eq_BitsTriple] at h1
    have := FloatFormat.exponentBits_pos
    have := BitVec.zero_ne_allOnes (by omega) h1.left
    contradiction
  · unfold FloatBits.isInfinite FloatBits.isExponentAllOnes at h2
    rw [FloatBits.zero_def', FloatBits.construct_exponent_eq_BitsTriple] at h2
    have := FloatFormat.exponentBits_pos
    have := BitVec.zero_ne_allOnes (by omega) h2.left
    contradiction
  · norm_num
    unfold FloatBits.FpExponent FloatBits.FpSignificand
    simp_rw [Fp.zero_def, FloatBits.zero_def', FloatBits.construct_sign_eq_BitsTriple, FloatBits.construct_significand_eq_BitsTriple, FloatBits.construct_exponent_eq_BitsTriple]
    simp_all only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, pow_one, Nat.zero_mod, Nat.reduceBEq, ↓reduceIte,
      finite.injEq]
    rfl

-- TODO: uniqueness of ±0

theorem toBits_ofBits [StdFloatFormat] (f : Fp) : ofBits (toBits f).representative = f := by
  if hn : f.isNaN then
    sorry
  else if hi : f.isInfinite then
    sorry
  else
    sorry



end Fp

def f := @FiniteFp.toRat FloatFormat.Binary32.toFloatFormat
#eval! f (0 : @FiniteFp FloatFormat.Binary32.toFloatFormat)
def f' := @Fp.toBits FloatFormat.Binary32.toFloatFormat
def v := f' (0 : @Fp FloatFormat.Binary32.toFloatFormat)
-- #eval! @Fp.FpQuotient.representative FloatFormat.Binary32 v FloatFormat.binary32_standard_exp_range
-- #eval! (@toBits FloatFormat.Binary32 (0 : @Fp FloatFormat.Binary32) FloatFormat.binary32_standard_exp_range).representative

#eval (@Fp.toRat? FloatFormat.Binary16.toFloatFormat) (@Fp.ofBits FloatFormat.Binary16 (0 : @Fp.FloatBits FloatFormat.Binary16.toFloatFormat))
