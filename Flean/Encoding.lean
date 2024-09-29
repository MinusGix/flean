import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets

import Flean.Basic
import Flean.BitVecUtil

namespace Fp

-- TODO: It would be interesting to have a softfloat implementation that operates on bits
-- rather than the triples.

-- TODO: when converting NaNs to floats should we instead convert to a Quotient type over the bit representations
-- to be very explicit about there not being a strict single NaN value?

section BitSize
-- variable [F : FloatFormat]

@[reducible]
def FloatFormat.signBits : ℕ := 1

@[reducible]
def FloatFormat.significandBits [FloatFormat] : ℕ :=
  FloatFormat.prec - 1

theorem FloatFormat.significandBits_ge_one [FloatFormat] :
  FloatFormat.significandBits ≥ 1 := by
  unfold FloatFormat.significandBits
  have := FloatFormat.valid_prec
  omega

theorem FloatFormat.significandBits_pos [FloatFormat] :
  FloatFormat.significandBits > 0 := by
  have := FloatFormat.significandBits_ge_one
  omega

@[reducible]
def FloatFormat.exponentRange [FloatFormat] : ℤ :=
  FloatFormat.max_exp - FloatFormat.min_exp + 1

@[reducible]
def FloatFormat.exponentBits [FloatFormat] : ℕ :=
  Nat.log2 ((FloatFormat.exponentRange).toNat - 1) + 1

@[simp]
theorem FloatFormat.exponentRange_nonneg [FloatFormat] :
  FloatFormat.exponentRange ≥ 0 := by
  simp only [exponentRange, ge_iff_le]
  have h := FloatFormat.valid_exp
  omega

@[simp]
theorem FloatFormat.exponentBits_pos [FloatFormat] :
  FloatFormat.exponentBits > 0 := by
  unfold FloatFormat.exponentBits
  have := FloatFormat.valid_exp
  omega

@[reducible]
def FloatFormat.bitSize [FloatFormat] : ℕ :=
  if FloatFormat.radix = Radix.Binary then
    -- 1 for the sign bit, F.prec - 1 for the significand, and F.prec for the exponent
    -- we can skip 1 bit because we don't need to represent the leading 1/0 in the significand
    FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits
  else
    -- TODO: How do you compute this for the decimal format, or other cases?
    -- Should we have this be in the units that the radix is defined in, instead of general bits?
    0

def FloatFormat.bitSize_eq_binary [FloatFormat] (h : FloatFormat.radix = Radix.Binary) :
  FloatFormat.bitSize = FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits := by
  simp only [FloatFormat.bitSize, h, ↓reduceIte]

/-- Added to the exponent to make the biased exponent, a non-negative number -/
@[reducible]
def FloatFormat.exponentBias [FloatFormat] : ℤ :=
  FloatFormat.max_exp

-- TODO: any ways to weaken this for non-standard exp values?
theorem FloatFormat.exponentBias_add_standard_pos [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  e + FloatFormat.exponentBias > 0 := by
  unfold FloatFormat.exponentBias
  unfold FloatFormat.isStandardExpRange at standard
  omega

theorem FloatFormat.exponentBias_add_standard_nonneg [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  e + FloatFormat.exponentBias ≥ 0 := by
  unfold FloatFormat.exponentBias
  unfold FloatFormat.isStandardExpRange at standard
  omega

/-- The biased exponent as a nat is equivalent to the biased exponent as an int -/
theorem FloatFormat.exponentBias_add_standard_toNat [FloatFormat] (e : ℤ) (e_range : FloatFormat.min_exp ≤ e ∧ e ≤ FloatFormat.max_exp) (standard : FloatFormat.isStandardExpRange) :
  ↑(e + FloatFormat.exponentBias).toNat = e + FloatFormat.exponentBias := by
  apply Int.toNat_of_nonneg
  exact FloatFormat.exponentBias_add_standard_nonneg e e_range standard

end BitSize

-- TODO: RFL can solve these, but the speed is very slow.
theorem FloatFormat.Binary16.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary16 = 16 := by
  native_decide

theorem FloatFormat.Binary32.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary32 = 32 := by
  native_decide

theorem FloatFormat.Binary64.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary64 = 64 := by
  native_decide

theorem FloatFormat.Binary128.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.Binary128 = 128 := by
  native_decide

theorem FloatFormat.BF16.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.BF16 = 16 := by
  native_decide

theorem FloatFormat.TF32.bitSize_eq :
  @FloatFormat.bitSize FloatFormat.TF32 = 19 := by
  native_decide

-- TODO: Should the FloatBits be specialized to binary representation? It would make the logic simpler, especially as I haven't considered how decimal floats are encoded in the first place.

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

end FloatBitsTriple

namespace FloatBits

variable [FloatFormat]

def mk' (sign : BitVec FloatFormat.signBits) (exponent : BitVec FloatFormat.exponentBits) (significand : BitVec FloatFormat.significandBits) : FloatBits :=
  if hr : FloatFormat.radix = Radix.Binary then
    let b := sign ++ exponent ++ significand
    {b := BitVec.cast (FloatFormat.bitSize_eq_binary hr).symm b}
  else
    {b := 0}

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

theorem appendToBitsTriple_eq (hr : FloatFormat.radix = Radix.Binary) (t : FloatBitsTriple) : (b : FloatBits) → b.toBitsTriple = t → b = FloatBits.mk' t.sign t.exponent t.significand := by
  intro b h
  unfold FloatBits.toBitsTriple at h
  lift_lets at h

  subst h
  norm_num

  unfold FloatBits.mk'
  unfold FloatFormat.bitSize
  split_ifs
  apply (ext1 _ _).mpr

  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]

  let bb' : BitVec (FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits) := BitVec.cast (FloatFormat.bitSize_eq_binary hr) b.b
  have bz := @BitVec.extractBreakup₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits bb'
  rw [add_comm FloatFormat.exponentBits] at bz

  rw [BitVec.cast_eq_swap (FloatFormat.bitSize_eq_binary hr)]
  repeat rw [← BitVec.extractLsb'_cast (FloatFormat.bitSize_eq_binary hr)]
  unfold_let bb' at bz
  rw [bz]

def toValueTriple (b : FloatBits) : Bool × ℤ × ℤ :=
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  let sign := if sign == 1 then true else false
  let exponent := exponent.toNat
  let significand := significand.toNat
  (sign, exponent, significand)

def sign (b : FloatBits) : Bool := b.toBitsTriple.sign == 1

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

/-- Constructing a `FloatBitsTriple` from a `FloatBits` made by `(s, E, T)` will yield the same `(s, E, T)` -/
theorem construct_triple_eq_BitsTriple (hr : FloatFormat.radix = Radix.Binary) (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.sign = s ∧ (FloatBits.mk' s E T).toBitsTriple.exponent = E ∧ (FloatBits.mk' s E T).toBitsTriple.significand = T := by
  unfold FloatBits.mk' FloatBits.toBitsTriple
  lift_lets
  norm_num
  split_ifs
  unfold FloatFormat.signBits
  -- Is there no way to use omega to simplify?
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]

  have kh : 1 + FloatFormat.exponentBits + FloatFormat.significandBits = FloatFormat.bitSize := by
    unfold FloatFormat.bitSize
    split_ifs
    linarith

  -- Simplify the casts out
  have k0 := λ (off size) => BitVec.extractLsb'_cast kh off size (s ++ E ++ T)
  have kS := k0 (FloatFormat.significandBits + FloatFormat.exponentBits) FloatFormat.signBits
  have kE := k0 FloatFormat.significandBits FloatFormat.exponentBits
  have kT := k0 0 FloatFormat.significandBits
  rw [kE, kT, kS]

  have jS := @BitVec.extractAppend_third₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  have jE := @BitVec.extractAppend_second₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  have jT := @BitVec.extractAppend_first₃ FloatFormat.signBits FloatFormat.exponentBits FloatFormat.significandBits s E T
  rw [jE, jT, jS]
  repeat1 constructor

theorem construct_sign_eq_BitsTriple (hr : FloatFormat.radix = Radix.Binary) (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.sign = s := (construct_triple_eq_BitsTriple hr s E T).1

theorem construct_exponent_eq_BitsTriple (hr : FloatFormat.radix = Radix.Binary) (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.exponent = E := (construct_triple_eq_BitsTriple hr s E T).2.1

theorem construct_significand_eq_BitsTriple (hr : FloatFormat.radix = Radix.Binary) (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.significand = T := (construct_triple_eq_BitsTriple hr s E T).2.2

/-- Get the bit representation of an infinite float. -/
def infinite (b : Bool) : FloatBits :=
  if FloatFormat.radix = Radix.Binary then
    let sign := BitVec.ofBool b
    let significand := BitVec.ofNat FloatFormat.significandBits 0
    let exponent := BitVec.allOnes FloatFormat.exponentBits
    FloatBits.mk' sign exponent significand
  else
    FloatBits.mk 0

/-- Constructing an infinite float will yield an infinite float. -/
theorem infinite_isInfinite (hr : FloatFormat.radix = Radix.Binary) (b : Bool) :
  (infinite b).isInfinite := by
  unfold FloatBits.isInfinite FloatBits.isExponentAllOnes FloatBits.isTSignificandZero FloatBits.infinite
  split_ifs
  norm_num
  rw [BitVec.ofNat_eq_ofNat]
  constructor
  · rw [construct_exponent_eq_BitsTriple hr]
  · rw [construct_significand_eq_BitsTriple hr]

theorem isInfinite_val (b : FloatBits) (hr : FloatFormat.radix = Radix.Binary) : b.isInfinite ↔ b = FloatBits.infinite true ∨ b = FloatBits.infinite false := by
  constructor
  · unfold FloatBits.isInfinite FloatBits.infinite
    intro ⟨he, hsig⟩
    split_ifs
    norm_num
    cases (BitVec.one_or b.toBitsTriple.sign)
    <;> {
      rename_i h0
      have h1 : b.toBitsTriple = FloatBitsTriple.mk (b.toBitsTriple.sign) (BitVec.allOnes FloatFormat.exponentBits) 0 := by
        apply (FloatBitsTriple.ext' _ _).mpr
        repeat1 constructor
        <;> norm_num
        assumption; assumption

      have k := FloatBits.appendToBitsTriple_eq hr _ b h1
      rw [h0] at k
      simp only [k, BitVec.ofNat_eq_ofNat, or_true, true_or]
    }
  · intro hv
    apply Or.elim hv
    <;> {
      intro hv
      rw [hv]
      apply infinite_isInfinite hr
    }

/-- Construct a NaN with the given sign bit and significand. -/
def NaN (sign : Bool) (T : BitVec FloatFormat.significandBits) (_hT : T ≠ 0): FloatBits :=
  if FloatFormat.radix = Radix.Binary then
    let sign := BitVec.ofBool sign
    let significand := T
    let exponent := BitVec.allOnes FloatFormat.exponentBits
    FloatBits.mk' sign exponent significand
  else
    FloatBits.mk 0

/-- Constructing a NaN will yield a NaN. -/
theorem NaN_isNaN (hr : FloatFormat.radix = Radix.Binary) (sign : Bool) (T : BitVec FloatFormat.significandBits) (hT : T ≠ 0):
  (NaN sign T hT).isNaN := by
  unfold FloatBits.isNaN FloatBits.isExponentAllOnes FloatBits.NaN
  split_ifs
  norm_num
  constructor
  · rw [construct_exponent_eq_BitsTriple hr]
  · rw [construct_significand_eq_BitsTriple hr]
    trivial

-- TODO: proof for finite floats that we are able to fit the values into the bits, that is, `.toNat` on the fields will return the original value

def sigToTrailing (m : ℕ) := m &&& (2^FloatFormat.significandBits - 1)

/-- Construct a finite float from the sign, exponent, and integral significand. -/
def finite (s : Bool) (e : ℤ) (m : ℕ) : FloatBits :=
  if FloatFormat.radix = Radix.Binary then
    -- Biased exponent
    let E := e + FloatFormat.exponentBias
    let E := E.toNat
    -- TODO: we aren't doing this dependent on the Nat which likely makes it harder to infer that it is necessary
    -- Trailing significand. We can cut off the leading bit because that is entangled with the exponent's value.
    let T := sigToTrailing m
    let sign := BitVec.ofBool s
    let significand := BitVec.ofNat FloatFormat.significandBits T
    let exponent := BitVec.ofNat FloatFormat.exponentBits E
    FloatBits.mk' sign exponent significand
  else
    FloatBits.mk 0

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

end FloatBits

instance [FloatFormat] {f : FloatBits} : Decidable f.isNaN := by
  unfold FloatBits.isNaN FloatBits.isExponentAllOnes
  infer_instance

def FpEquiv [FloatFormat] (x y : FloatBits) : Prop := x = y ∨ (x.isNaN ∧ y.isNaN)

instance [FloatFormat] : DecidableRel FpEquiv := by
  intro x y
  unfold FpEquiv
  infer_instance



-- TODO: proof that a = b ↔ a.toBits ≃ b.toBits
/-! A setoid which considers equivalence like how `Fp` does, treating NaNs as equivalent -/
def FpSetoid [FloatFormat] : Setoid FloatBits where
  /- If they're both NaN we consider them equivalent (in the higher level representation of Fp)-/
  r := FpEquiv
  iseqv := {
    refl := by
      intro x
      unfold FpEquiv FloatBits.isNaN
      left
      rfl
    symm := by
      unfold FpEquiv
      intro x y h
      cases h with
      | inl h_1 => subst h_1; left; rfl
      | inr h_2 => right; symm; exact h_2
    trans := by
      unfold FpEquiv
      intro x y z h1 h2
      cases h1 with
      | inl h =>
        cases h2 with
        | inl h_1 =>
          subst h h_1; left; rfl
        | inr h_2 => subst h; right; exact h_2
      | inr h_1 =>
        cases h2 with
        | inl h => subst h; right; exact h_1
        | inr h_2 =>
          right
          obtain ⟨⟨left1, right1⟩, _⟩ := h_1
          obtain ⟨_, right2⟩ := h_2

          unfold FloatBits.isTSignificandZero at right1
          apply And.intro
          · apply And.intro
            · assumption
            · simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_false_eq_true]
          · assumption
  }

def FpQuotient [FloatFormat] : Type := Quotient FpSetoid

-- TODO: it may be possible to have a general way to turn a proof that applies to `Fp` and make it apply to `FpQuotient`..

@[reducible]
def FpQuotient.isInfinite [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f (fun b => b.isInfinite) (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      unfold FloatBits.isInfinite
      unfold FloatBits.isNaN at h
      simp only [h, and_false]
  )

@[reducible]
def FpQuotient.isNaN [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f (fun b => b.isNaN) (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      simp only [h]
  )

def FpQuotient.isFinite [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f (fun b => b.isFinite) (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      unfold FloatBits.isFinite
      simp only [h, not_true_eq_false, false_and]
  )

-- Normal `sign` can't be equivalent over the quotient because two NaN values can have different signs
-- We simply say that an FpQuotient sign is always positive for NaN values, but doing such in FloatBits would be confusing.
def FpQuotient.fake_sign [FloatFormat] (f : FpQuotient) : Bool :=
  Quotient.liftOn f (fun b => b.fake_sign) (by
    intro a b h
    cases h with
    | inl h =>
      subst h
      simp only [FloatBits.sign, true_and]
    | inr h =>
      unfold FloatBits.fake_sign
      simp only [h, ↓reduceIte]
  )

noncomputable
def FpQuotient.choose [FloatFormat] (f : FpQuotient) : FloatBits :=
  @Quotient.out _ FpSetoid f

/-! Get a concrete bit pattern for the float, using a fixed representation for NaN values. -/
def FpQuotient.representative [FloatFormat] (f : FpQuotient) (standard : FloatFormat.isStandardExpRange) : FloatBits :=
  if f.isNaN then
    -- TODO: Make sure this isn't a signaling NaN
    have nz : BitVec.allOnes FloatFormat.significandBits ≠ 0 := by
      unfold FloatFormat.significandBits
      apply BitVec.allOnes_ne_zero
      have h := FloatFormat.valid_prec
      omega
    FloatBits.NaN false (BitVec.allOnes FloatFormat.significandBits) nz
  else if f.isInfinite then
    sorry
  else
    sorry


-- theorem FpQuotient.representative_eq [FloatFormat] (f : FpQuotient) : f = ⟦FpQuotient.representative f⟧ := by
--   unfold FpQuotient.representative
--   split_ifs
--   simp only [Quotient.eq, FpEquiv]
--   sorry
--   sorry


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
def ofBits [FloatFormat] (b : FloatBits) : Fp := by
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  sorry

-- TODO: proof that we can convert bitsFloatTriple back to bits

-- TODO: have proofs that these are approximately inverses (except for NaN)
-- we can have subproofs for each of finite/infinite/nan

-- TODO: proof about the number of finite floats, the number of finite floats in a certain range, etc.

end Fp

def f := @FiniteFp.toRat FloatFormat.Binary32
#eval! f (0 : @FiniteFp FloatFormat.Binary32)
def f' := @Fp.toBits FloatFormat.Binary32
def v := f' (0 : @Fp FloatFormat.Binary32)
-- #eval! @Fp.FpQuotient.representative FloatFormat.Binary32 v FloatFormat.binary32_standard_exp_range
-- #eval! (@toBits FloatFormat.Binary32 (0 : @Fp FloatFormat.Binary32) FloatFormat.binary32_standard_exp_range).representative
