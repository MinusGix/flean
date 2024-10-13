import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.Rify
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic
import Flean.BitVecUtil
import Flean.Encoding.BitSize
import Flean.Encoding.Util

namespace Fp

/-! Not guaranteed to be a valid float. Intended to have utility functions. -/
@[ext]
structure FloatBits [FloatFormat] where
  /-- `[sign S][biased exponent E][trailing significand T]` -/
  b: BitVec FloatFormat.bitSize
deriving Repr, DecidableEq -- TODO: actual usable repr

@[ext]
structure FloatBitsTriple [FloatFormat] where
  sign: BitVec FloatFormat.signBits
  /-- Biased exponent -/
  exponent: BitVec FloatFormat.exponentBits
  /-- Trailing significand -/
  significand: BitVec FloatFormat.significandBits
deriving Repr, DecidableEq

namespace FloatBitsTriple

-- More useful ext than the bitvec extensionality `@[ext]` seems to utilize
def ext' [FloatFormat] (t c : FloatBitsTriple) : t = c ↔ t.sign = c.sign ∧ t.exponent = c.exponent ∧ t.significand = c.significand := by
  apply Iff.intro
  · intro a
    subst a
    trivial
  · intro ⟨a1, a2, a3⟩
    ext1
    · rw [a1]
    · rw [a2]
    · rw [a3]

def sign' [FloatFormat] (t : FloatBitsTriple) : Bool := t.sign == 1

end FloatBitsTriple

namespace FloatBits

variable [FloatFormat]

def mk' (sign : BitVec FloatFormat.signBits) (exponent : BitVec FloatFormat.exponentBits) (significand : BitVec FloatFormat.significandBits) : FloatBits :=
  let b := sign ++ exponent ++ significand
  {b := BitVec.cast FloatFormat.bitSize_eq.symm b}

instance : Zero FloatBits := ⟨FloatBits.mk (0 : BitVec FloatFormat.bitSize)⟩

instance : Inhabited FloatBits := ⟨0⟩

theorem zero_def : (0 : FloatBits) = FloatBits.mk (0 : BitVec FloatFormat.bitSize) := rfl

theorem zero_def' : (0 : FloatBits) = FloatBits.mk' (0 : BitVec FloatFormat.signBits) (0 : BitVec FloatFormat.exponentBits) (0 : BitVec FloatFormat.significandBits) := by
  rw [zero_def]
  unfold mk'
  norm_num
  rw [BitVec.ofNat_eq_ofNat]
  ext1 i
  simp_all only [BitVec.getLsb_zero, BitVec.ofNat_eq_ofNat, BitVec.getLsb_append, Bool.cond_self]



def ext1 (b : FloatBits) (c : BitVec FloatFormat.bitSize) : b = ⟨c⟩ ↔ b.b = c := by
  constructor
  <;> intro a
  <;> subst a
  <;> simp_all only

def toBitsTriple (b : FloatBits) : FloatBitsTriple :=
  let b := b.b
  let sign := b.extractLsb' (FloatFormat.bitSize - FloatFormat.signBits) FloatFormat.signBits
  let exponent := b.extractLsb' (FloatFormat.bitSize - FloatFormat.exponentBits - FloatFormat.signBits) FloatFormat.exponentBits
  let significand := b.extractLsb' 0 FloatFormat.significandBits
  {sign := sign, exponent := exponent, significand := significand}




theorem appendToBitsTriple_eq (t : FloatBitsTriple) : (b : FloatBits) → b.toBitsTriple = t → b = FloatBits.mk' t.sign t.exponent t.significand := by
  intro b h
  unfold FloatBits.toBitsTriple at h
  lift_lets at h

  subst h
  norm_num

  unfold FloatBits.mk'
  unfold FloatFormat.bitSize
  apply (ext1 _ _).mpr

  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]

  let bb' : BitVec (FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits) := BitVec.cast FloatFormat.bitSize_eq.symm b.b
  have bz := @BitVec.extractBreakup₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits bb'
  rw [add_comm FloatFormat.exponentBits] at bz

  rw [BitVec.cast_eq_swap (FloatFormat.bitSize_eq)]
  unfold_let bb' at bz
  -- We run into the issue that it will just nest the cast inside the cast when we apply it again, is there a better way?
  rw [← BitVec.extractLsb'_cast (FloatFormat.bitSize_eq)]
  conv =>
    rhs
    rhs
    rw [← BitVec.extractLsb'_cast (FloatFormat.bitSize_eq)]
  conv =>
    rhs
    lhs
    rhs
    rw [← BitVec.extractLsb'_cast (FloatFormat.bitSize_eq)]
  rw [bz]

def ext_triple (b c : FloatBits) : b = c ↔ b.toBitsTriple = c.toBitsTriple := by
  apply Iff.intro
  · intro a
    subst a
    trivial
  · intro h
    have j := appendToBitsTriple_eq c.toBitsTriple b h
    rw [j]
    symm
    apply appendToBitsTriple_eq
    rfl

def ext_triple' (b c : FloatBits) : b = c ↔ b.toBitsTriple.sign = c.toBitsTriple.sign ∧ b.toBitsTriple.exponent = c.toBitsTriple.exponent ∧ b.toBitsTriple.significand = c.toBitsTriple.significand := by
  apply Iff.intro
  · intro a
    subst a
    trivial
  · intro h
    apply (ext_triple b c).mpr
    apply (FloatBitsTriple.ext' _ _).mpr
    exact h

def toValueTriple (b : FloatBits) : Bool × ℤ × ℤ :=
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  let sign := if sign == 1 then true else false
  let exponent := exponent.toNat
  let significand := significand.toNat
  (sign, exponent, significand)

def sign (b : FloatBits) : Bool := b.toBitsTriple.sign == 1

def sign' (b : FloatBits) : BitVec FloatFormat.signBits := b.toBitsTriple.sign

abbrev isExponentAllOnes (b : FloatBits) : Prop := b.toBitsTriple.exponent = BitVec.allOnes FloatFormat.exponentBits

-- TODO: replace these annoying clutter instances with some sort of derive
instance [FloatFormat] : DecidablePred FloatBits.isExponentAllOnes := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.toBitsTriple.exponent = BitVec.allOnes FloatFormat.exponentBits))

/-- The exponent being all ones means that it is equivalent to 2^W - 1 -/
def isExponentAllOnes_eq_ofNat (b : FloatBits) : b.isExponentAllOnes ↔ b.toBitsTriple.exponent.toNat = (2^FloatFormat.exponentBits - 1) := by
  unfold isExponentAllOnes
  unfold BitVec.allOnes BitVec.toNat
  constructor
  <;> intro h
  · rw [h]
    simp only [BitVec.val_toFin, BitVec.toNat_ofNatLt]
  · ext
    rw [BitVec.val_toFin] at h
    simp only [BitVec.getLsb, h, Nat.testBit_two_pow_sub_one, Fin.is_lt, decide_True,
      BitVec.toNat_ofNatLt]

-- TODO: probably get rid of this. We should justh have a `.significand` method that does the conversion to bitstriple inside it
@[reducible]
def isTSignificandZero (b : FloatBits) : Prop := b.toBitsTriple.significand = 0

def isNaN (b : FloatBits) : Prop := b.isExponentAllOnes ∧ ¬b.isTSignificandZero
-- TODO qNaN vs sNaN

instance [FloatFormat] : DecidablePred FloatBits.isNaN := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.isExponentAllOnes ∧ ¬b.isTSignificandZero))

-- set_option diagnostics true

/-- Assigns all NaN values a positive sign. Used mostly for FpQuotient. -/
def fake_sign (b : FloatBits) : Bool := if b.isNaN then false else b.sign

def isInfinite (b : FloatBits) : Prop := b.isExponentAllOnes ∧ b.isTSignificandZero

instance [FloatFormat] : DecidablePred FloatBits.isInfinite := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.isExponentAllOnes ∧ b.isTSignificandZero))

def isZero (b : FloatBits) : Prop := b.toBitsTriple.exponent = 0 ∧ b.isTSignificandZero

instance [FloatFormat] : DecidablePred FloatBits.isZero := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.toBitsTriple.exponent = 0 ∧ b.isTSignificandZero))

def isFinite (b : FloatBits) : Prop := ¬b.isNaN ∧ ¬b.isInfinite

instance [FloatFormat] : DecidablePred FloatBits.isFinite := inferInstanceAs (DecidablePred (λ (b : FloatBits) => ¬b.isNaN ∧ ¬b.isInfinite))

def isSubnormal (b : FloatBits) : Prop := b.toBitsTriple.exponent = 0 ∧ ¬b.isTSignificandZero

instance [FloatFormat] : DecidablePred FloatBits.isSubnormal := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.toBitsTriple.exponent = 0 ∧ ¬b.isTSignificandZero))

def isNormal (b : FloatBits) : Prop := b.toBitsTriple.exponent ≠ 0 ∧ ¬b.isExponentAllOnes

instance [FloatFormat] : DecidablePred FloatBits.isNormal := inferInstanceAs (DecidablePred (λ (b : FloatBits) => b.toBitsTriple.exponent ≠ 0 ∧ ¬b.isExponentAllOnes))

theorem isFinite_def' (b : FloatBits) : b.isFinite ↔ b.isZero ∨ b.isNormal ∨ b.isSubnormal := by
  unfold FloatBits.isFinite FloatBits.isNaN FloatBits.isInfinite FloatBits.isZero FloatBits.isNormal FloatBits.isSubnormal
  unfold FloatBits.isExponentAllOnes FloatBits.isTSignificandZero
  constructor
  · intro hfin

    if h1 : b.toBitsTriple.exponent = 0 then
      simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_and, Decidable.not_not, true_and,
        not_true_eq_false, false_and, false_or]
      by_cases b.toBitsTriple.significand = 0
      <;> simp_all only [BitVec.ofNat_eq_ofNat, implies_true, not_true_eq_false, imp_false,
        true_and, or_false, not_false_eq_true, or_true]
    else
      by_cases b.toBitsTriple.significand = 0
      <;> simp_all only [BitVec.ofNat_eq_ofNat, not_true_eq_false, and_false, not_false_eq_true,
          and_true, true_and, ne_eq, and_self, or_false, or_true]
  · intro h
    if h1 : b.toBitsTriple.exponent = 0 then
      simp_all only [BitVec.ofNat_eq_ofNat, true_and, ne_eq, not_true_eq_false, false_and, false_or,
        not_and, Decidable.not_not]
      have := FloatFormat.exponentBits_pos
      by_cases b.toBitsTriple.significand = 0
      <;> {
        simp_all only [BitVec.ofNat_eq_ofNat, not_true_eq_false, or_false, implies_true, imp_false, true_and, not_false_eq_true, and_true]
        rw [← ne_eq]
        symm
        apply BitVec.allOnes_ne_zero
        omega
      }
    else
      simp_all only [BitVec.ofNat_eq_ofNat, ne_eq, not_and, Decidable.not_not, false_and,
        not_false_eq_true, true_and, or_false, false_or, false_implies, and_self]

theorem isZero_notSubnormal (b : FloatBits) : b.isZero → ¬b.isSubnormal := by
  unfold FloatBits.isSubnormal FloatBits.isZero
  intro h
  simp only [h, BitVec.ofNat_eq_ofNat, ne_eq, not_true_eq_false, and_false, not_false_eq_true]

theorem isZero_notNormal (b : FloatBits) : b.isZero → ¬b.isNormal := by
  unfold FloatBits.isNormal FloatBits.isZero
  intro h
  simp only [h, BitVec.ofNat_eq_ofNat, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

@[simp]
theorem isNaN_notInfinite (b : FloatBits) : b.isNaN → ¬b.isInfinite := by
  unfold FloatBits.isNaN FloatBits.isInfinite
  intro h
  simp only [h, and_false, not_false_eq_true]

@[simp]
theorem isNaN_notFinite (b : FloatBits) : b.isNaN → ¬b.isFinite := by
  unfold FloatBits.isFinite FloatBits.isNaN FloatBits.isInfinite
  intro h
  simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_false_eq_true, and_true, not_true_eq_false,
    not_and, implies_true]

@[simp]
theorem isInfinite_notNaN (b : FloatBits) : b.isInfinite → ¬b.isNaN := by
  unfold FloatBits.isNaN FloatBits.isInfinite
  intro h
  simp only [h, ne_eq, BitVec.ofNat_eq_ofNat, not_true_eq_false, and_false, not_false_eq_true]

@[simp]
theorem isInfinite_notFinite (b : FloatBits) : b.isInfinite → ¬b.isFinite := by
  unfold FloatBits.isFinite FloatBits.isInfinite FloatBits.isNaN
  intro h
  simp only [ne_eq, h, BitVec.ofNat_eq_ofNat, not_true_eq_false, and_false, not_false_eq_true,
    not_and, imp_false]

@[simp]
theorem isFinite_notNaN (b : FloatBits) : b.isFinite → ¬b.isNaN := λ h => h.left

@[simp]
theorem isFinite_notInfinite (b : FloatBits) : b.isFinite → ¬b.isInfinite := λ h => h.right

theorem isFinite_exponent_not_allOnes (b : FloatBits) : b.isFinite → ¬b.isExponentAllOnes := by
  intro hf he
  have := not_not.mp (not_and.mp (b.isFinite_notNaN hf) he)
  have := not_and.mp (b.isFinite_notInfinite hf) he
  contradiction

@[simp]
theorem notAll (b : FloatBits) : ¬(b.isNaN ∧ b.isInfinite ∧ b.isFinite) := by
  intro ⟨h1, h2⟩
  simp_all only [isNaN, ne_eq, BitVec.ofNat_eq_ofNat, isInfinite, isFinite, not_true_eq_false,
    and_false]


theorem cases (b : FloatBits) : b.isNaN ∨ b.isInfinite ∨ b.isFinite := by
  by_cases b.isNaN
  · left
    assumption
  · by_cases b.isInfinite
    · right; left
      assumption
    · unfold FloatBits.isNaN FloatBits.isInfinite FloatBits.isFinite
      simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_false_eq_true, and_self, or_true]


-- You may want to use this with `notAll`
theorem disj (b : FloatBits) : (Xor' (Xor' b.isNaN b.isInfinite) b.isFinite) := by
  if h1 : b.isFinite then
    simp only [h1, isFinite_notNaN, isFinite_notInfinite, xor_self, xor_false, id_eq]
  else
    constructor
    if h2 : b.isNaN then
      simp_all only [isNaN_notFinite, not_false_eq_true, isNaN_notInfinite, xor_true, and_self]
    else
      simp_all only [isFinite, isNaN, isExponentAllOnes, isTSignificandZero, BitVec.ofNat_eq_ofNat,
        not_and, Decidable.not_not, isInfinite, not_true_eq_false, imp_false, implies_true,
        and_false, and_self, xor_false, id_eq, not_false_eq_true]
-- TODO: disj between nan, infinite, normal finite, subnormal finite and zero

theorem notNaN_notInfinite (b : FloatBits) : ¬b.isNaN → ¬b.isInfinite → b.isFinite := by
  unfold FloatBits.isFinite FloatBits.isNaN FloatBits.isInfinite
  intro h1 h2
  exact ⟨h1, h2⟩

/-- Constructing a `FloatBitsTriple` from a `FloatBits` made by `(s, E, T)` will yield the same `(s, E, T)` -/
theorem construct_triple_eq_BitsTriple (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.sign = s ∧ (FloatBits.mk' s E T).toBitsTriple.exponent = E ∧ (FloatBits.mk' s E T).toBitsTriple.significand = T := by
  unfold FloatBits.mk' FloatBits.toBitsTriple
  lift_lets
  norm_num
  unfold FloatFormat.signBits
  -- Is there no way to use omega to simplify?
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]

  have jS := @BitVec.extractAppend_third₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  have jE := @BitVec.extractAppend_second₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  have jT := @BitVec.extractAppend_first₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  rw [jE, jT, jS]
  repeat1 constructor

theorem construct_sign_eq_BitsTriple (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.sign = s := (construct_triple_eq_BitsTriple s E T).1

theorem construct_exponent_eq_BitsTriple (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.exponent = E := (construct_triple_eq_BitsTriple s E T).2.1

theorem construct_significand_eq_BitsTriple (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.significand = T := (construct_triple_eq_BitsTriple s E T).2.2

/-- Get the bit representation of an infinite float. -/
def infinite (b : Bool) : FloatBits :=
  let sign := BitVec.ofBool b
  let significand := BitVec.ofNat FloatFormat.significandBits 0
  let exponent := BitVec.allOnes FloatFormat.exponentBits
  FloatBits.mk' sign exponent significand

/-- Constructing an infinite float will yield an infinite float. -/
theorem infinite_isInfinite (b : Bool) :
  (infinite b).isInfinite := by
  unfold FloatBits.isInfinite FloatBits.isExponentAllOnes FloatBits.isTSignificandZero FloatBits.infinite
  norm_num
  rw [BitVec.ofNat_eq_ofNat]
  constructor
  · rw [construct_exponent_eq_BitsTriple]
  · rw [construct_significand_eq_BitsTriple]

theorem isInfinite_val (b : FloatBits) : b.isInfinite ↔ b = FloatBits.infinite true ∨ b = FloatBits.infinite false := by
  constructor
  · unfold FloatBits.isInfinite FloatBits.infinite
    intro ⟨he, hsig⟩
    norm_num
    cases (BitVec.one_or b.toBitsTriple.sign)
    <;> {
      rename_i h0
      have h1 : b.toBitsTriple = FloatBitsTriple.mk (b.toBitsTriple.sign) (BitVec.allOnes FloatFormat.exponentBits) 0 := by
        apply (FloatBitsTriple.ext' _ _).mpr
        repeat1 constructor
        <;> norm_num
        assumption; assumption

      have k := FloatBits.appendToBitsTriple_eq _ b h1
      rw [h0] at k
      simp only [k, BitVec.ofNat_eq_ofNat, or_true, true_or]
    }
  · intro hv
    apply Or.elim hv
    <;> {
      intro hv
      rw [hv]
      apply infinite_isInfinite
    }

theorem isInfinite_mk' (b : FloatBits) : b.isInfinite → b = FloatBits.mk' b.sign' (BitVec.allOnes _) 0 := by
  intro ⟨he, hsig⟩
  apply (ext_triple' _ _).mpr
  rw [construct_sign_eq_BitsTriple, construct_exponent_eq_BitsTriple, construct_significand_eq_BitsTriple]
  unfold sign'
  simp_all only [BitVec.ofNat_eq_ofNat, and_self]

/-- Construct a NaN with the given sign bit and significand. -/
def NaN (sign : Bool) (T : BitVec FloatFormat.significandBits) (_hT : T ≠ 0): FloatBits :=
  let sign := BitVec.ofBool sign
  let significand := T
  let exponent := BitVec.allOnes FloatFormat.exponentBits
  FloatBits.mk' sign exponent significand

/-- Constructing a NaN will yield a NaN. -/
@[simp]
theorem NaN_isNaN (sign : Bool) (T : BitVec FloatFormat.significandBits) (hT : T ≠ 0):
  (NaN sign T hT).isNaN := by
  unfold FloatBits.isNaN FloatBits.isExponentAllOnes FloatBits.NaN
  norm_num
  constructor
  · rw [construct_exponent_eq_BitsTriple]
  · rw [construct_significand_eq_BitsTriple]
    trivial

-- TODO: proof for finite floats that we are able to fit the values into the bits, that is, `.toNat` on the fields will return the original value

def sigToTrailing (m : ℕ) := m &&& (2^FloatFormat.significandBits - 1)

/-- Construct a finite float from the sign, exponent, and integral significand. -/
def finite (s : Bool) (e : ℤ) (m : ℕ) (_vf : IsValidFiniteVal e m) : FloatBits :=
  -- Biased exponent
  let E := if _root_.isSubnormal e m then 0 else e + FloatFormat.exponentBias
  let E := E.toNat
  let T := if _root_.isSubnormal e m then sigToTrailing m else m
  let sign := BitVec.ofBool s
  let significand := BitVec.ofNat FloatFormat.significandBits T
  let exponent := BitVec.ofNat FloatFormat.exponentBits E
  FloatBits.mk' sign exponent significand

@[simp]
theorem finite_sign (s : Bool) (e : ℤ) (m : ℕ) (vf : IsValidFiniteVal e m) : (finite s e m vf).sign = s := by
  unfold finite
  lift_lets
  unfold FloatBits.sign
  simp_rw [construct_sign_eq_BitsTriple]
  rw [BitVec.ofBool_beq_one]

@[simp]
theorem infinite_sign (b : Bool) : (infinite b).sign = b := by
  unfold infinite FloatBits.sign
  simp_all only [construct_sign_eq_BitsTriple, BitVec.ofBool_beq_one]

theorem validFiniteVal_biasedExponent_notAllOnes (st : FloatFormat.isStandardExpRange) (vf : IsValidFiniteVal e m) :
  ¬(BitVec.ofNat FloatFormat.exponentBits (e + FloatFormat.exponentBias).toNat = BitVec.allOnes _) := by
  unfold IsValidFiniteVal at vf
  intro h
  have l := (BitVec.ofNat FloatFormat.exponentBits (e + FloatFormat.exponentBias).toNat).isLt
  unfold FloatFormat.exponentBias at h l
  have h := (BitVec.toNat_eq _ _).mp h
  rw [BitVec.toNat_ofNat] at h l
  rw [BitVec.toNat_allOnes] at h
  have a0 : FloatFormat.max_exp.toNat + 1 ≤ 2^FloatFormat.exponentBits2 := Nat.le_pow_clog one_lt_two (FloatFormat.max_exp.toNat + 1)
  have ae_pos : e + FloatFormat.max_exp ≥ 0 := by
    -- TODO(minor): Not sure we actually need isStandardExpRange here
    rw [st] at vf
    omega
  have a4 : 2 * FloatFormat.max_exp.toNat + 2 ≤ 2^FloatFormat.exponentBits := by
    conv => lhs; rhs; rw [← mul_one 2]
    rw [← mul_add]
    apply FloatFormat.le_pow_exponentBits2_imp_double_le_exponentBits
    trivial
  have a6 : (e + FloatFormat.max_exp).toNat < 2 * FloatFormat.max_exp.toNat + 1 := by
    zify
    rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg]
    <;> omega
  have ae_le : (e + FloatFormat.max_exp).toNat ≤ 2 * FloatFormat.max_exp.toNat := by
    zify
    rw [Int.toNat_of_nonneg ae_pos, Int.toNat_of_nonneg FloatFormat.max_exp_pos.le]
    omega
  have a7 : (e + FloatFormat.max_exp).toNat < 2^FloatFormat.exponentBits - 1 := lt_of_le_of_lt ae_le (by omega)
  rw [Nat.mod_eq_of_lt (by omega)] at h
  rw [h] at a7
  exact (lt_self_iff_false _).mp a7

theorem finite_isNotNaN (s : Bool) (e : ℤ) (m : ℕ) (st : FloatFormat.isStandardExpRange) (vf : IsValidFiniteVal e m) :
  ¬(finite s e m vf).isNaN := by
  unfold FloatBits.isNaN FloatBits.finite FloatBits.isExponentAllOnes FloatBits.isTSignificandZero
  lift_lets
  extract_lets E1 E _ sign significand exponent
  rw [construct_exponent_eq_BitsTriple, construct_significand_eq_BitsTriple]
  unfold_let exponent E E1
  intro ⟨he, _⟩
  split_ifs at he
  · rw [Int.toNat_zero] at he
    have := BitVec.allOnes_ne_zero FloatFormat.exponentBits_nz
    symm at he
    contradiction
  · have := validFiniteVal_biasedExponent_notAllOnes st vf
    contradiction

theorem finite_isNotInfinite (s : Bool) (e : ℤ) (m : ℕ) (st : FloatFormat.isStandardExpRange) (vf : IsValidFiniteVal e m) :
  ¬(finite s e m vf).isInfinite := by
  unfold FloatBits.finite FloatBits.isInfinite FloatBits.isExponentAllOnes FloatBits.isTSignificandZero
  lift_lets
  extract_lets E1 E _ sign significand exponent
  rw [construct_exponent_eq_BitsTriple, construct_significand_eq_BitsTriple]
  unfold_let exponent E E1
  intro ⟨he, _⟩
  split_ifs at he
  · rw [Int.toNat_zero] at he
    have := BitVec.allOnes_ne_zero FloatFormat.exponentBits_nz
    symm at he
    contradiction
  · have := validFiniteVal_biasedExponent_notAllOnes st vf
    contradiction

theorem finite_isFinite (s : Bool) (e : ℤ) (m : ℕ) (st : FloatFormat.isStandardExpRange) (vf : IsValidFiniteVal e m) :
  (finite s e m vf).isFinite := ⟨(finite_isNotNaN s e m st vf), (finite_isNotInfinite s e m st vf)⟩

-- TODO: trailing to significand, takes E as well

theorem sigToTrailing_le (m : ℕ) : sigToTrailing m < 2^FloatFormat.significandBits := by
  unfold sigToTrailing
  rw [Nat.and_pow_two_is_mod]
  omega

/-- Converting to bitvec and back will yield the same number as the significandToTrailing function. Showing that we don't lose anything. -/
theorem sigToTrailing_eq_bits (m : ℕ) :
  (BitVec.ofNat FloatFormat.significandBits (sigToTrailing m)).toNat = sigToTrailing m := by
  apply (BitVec.toNat_eq_nat (BitVec.ofNat FloatFormat.significandBits (sigToTrailing m)) _).mpr
  constructor
  · exact sigToTrailing_le m
  · rfl

/-- Split up into the three components of the bit pattern, but treats NaN as the quotient representative. Mostly used for the `FpQuotient` type. -/
def fake_toBitsTriple [FloatFormat] (b : FloatBits) : FloatBitsTriple :=
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  if b.isNaN then
    -- Quotient representative for NaN values
    {sign := BitVec.ofBool false, exponent := BitVec.allOnes _, significand := BitVec.allOnes _ }
  else
    {sign := sign, exponent := exponent, significand := significand}

end FloatBits

end Fp
