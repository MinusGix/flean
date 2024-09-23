import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

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

@[reducible]

def FloatFormat.exponentRange [FloatFormat] : ℤ :=
  FloatFormat.max_exp - FloatFormat.min_exp + 1

@[reducible]
def FloatFormat.exponentBits [FloatFormat] : ℕ :=
  Nat.log2 ((FloatFormat.exponentRange).toNat - 1) + 1

theorem FloatFormat.exponentRange_nonneg [FloatFormat] :
  FloatFormat.exponentRange ≥ 0 := by
  simp [FloatFormat.exponentRange]
  have h := FloatFormat.valid_exp
  linarith


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

@[reducible]
instance [FloatFormat] : BEq FloatBits where
  beq := λ a b => a.b == b.b

instance [FloatFormat] : LawfulBEq FloatBits where
  eq_of_beq {a b} h := by
    ext
    unfold BEq.beq at h
    simp only at h
    simp_all only [beq_iff_eq]
  rfl {a} := by
    unfold BEq.beq
    simp only [beq_self_eq_true]

@[ext]
structure FloatBitsTriple [FloatFormat] where
  sign: BitVec FloatFormat.signBits
  /-- Biased exponent -/
  exponent: BitVec FloatFormat.exponentBits
  /-- Trailing significand -/
  significand: BitVec FloatFormat.significandBits
deriving Repr, DecidableEq

@[reducible]
instance [FloatFormat] : BEq FloatBitsTriple where
  beq := λ a b => a.sign == b.sign ∧ a.exponent == b.exponent ∧ a.significand == b.significand

instance [FloatFormat] : LawfulBEq FloatBitsTriple where
  eq_of_beq {a b} h := by
    -- ext
    unfold BEq.beq at h
    simp only [beq_iff_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h
    ext1
    exact h.1
    exact h.2.1
    exact h.2.2
  rfl {a} := by
    simp only [BEq.beq, decide_True, and_self]

namespace FloatBits

variable [FloatFormat]

-- def mk' (sign : BitVec FloatFormat.signBits) (exponent : BitVec FloatFormat.exponentBits) (significand : BitVec FloatFormat.significandBits) : FloatBits := by
--   -- TODO: this shouldn't be in proof mode
--   constructor
--   unfold FloatFormat.bitSize
--   if hr: FloatFormat.radix == Radix.Binary then
--     simp only [LawfulBEq.eq_of_beq hr, ↓reduceIte]
--     exact sign ++ exponent ++ significand
--   else
--     exact 0

def mk' (sign : BitVec FloatFormat.signBits) (exponent : BitVec FloatFormat.exponentBits) (significand : BitVec FloatFormat.significandBits) : FloatBits :=
  if hr : FloatFormat.radix = Radix.Binary then
    let b := sign ++ exponent ++ significand
    {b := BitVec.cast (FloatFormat.bitSize_eq_binary hr).symm b}
  else
    {b := 0}


def toBitsTriple (b : FloatBits) : FloatBitsTriple :=
  let b := b.b
  let sign := b.extractLsb' (FloatFormat.bitSize - 1) 1
  let exponent := b.extractLsb' (FloatFormat.bitSize - FloatFormat.exponentBits - 1) FloatFormat.exponentBits
  let significand := b.extractLsb' 0 FloatFormat.significandBits
  {sign := sign, exponent := exponent, significand := significand}

theorem appendToBitsTriple_eq (t : FloatBitsTriple) : (b : FloatBits) → b.toBitsTriple = t → b = FloatBits.mk' t.sign t.exponent t.significand := by
  intro b h
  -- ext
  unfold FloatBits.toBitsTriple at h
  -- unfold FloatBits.mk'
  simp_all only
  if hr : FloatFormat.radix = Radix.Binary then
    -- simp only [hr, beq_self_eq_true, ↓reduceDIte, eq_mpr_eq_cast, id_eq]
    -- have hs : t.sign = BitVec.extractLsb' (FloatFormat.bitSize - 1) 1 b.b := by
    --   subst h
    subst h
    simp only

    unfold FloatBits.mk'
    unfold FloatFormat.bitSize
    simp only [hr, ↓reduceDIte, ↓reduceIte]
    unfold FloatFormat.signBits
    rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]
    rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]

    let bi := BitVec.extractLsb' (FloatFormat.significandBits + FloatFormat.exponentBits) 1 b.b ++
            BitVec.extractLsb' FloatFormat.significandBits FloatFormat.exponentBits b.b ++
          BitVec.extractLsb' 0 FloatFormat.significandBits b.b
    have hr' := FloatFormat.bitSize_eq_binary hr
    have ha : BitVec.cast hr'.symm bi = b.b := by
      unfold_let
      -- cases hr'.symm
      sorry
    sorry
  else
    sorry

theorem auxbv (hr : FloatFormat.radix = Radix.Binary) (h : FloatFormat.signBits + FloatFormat.exponentBits + FloatFormat.significandBits = FloatFormat.bitSize) (b : BitVec FloatFormat.bitSize) : BitVec.cast h
    (BitVec.extractLsb' (FloatFormat.significandBits + FloatFormat.exponentBits) 1 b ++
        BitVec.extractLsb' FloatFormat.significandBits FloatFormat.exponentBits b ++
      BitVec.extractLsb' 0 FloatFormat.significandBits b) = b := by
  -- unfold FloatFormat.signBits FloatFormat.significandBits FloatFormat.exponentBits at *
  -- have k := Decidable.rec
  -- cases h
  -- have j := BitVec.extractBreakup₃
  sorry
  -- rw [j]



def toValueTriple (b : FloatBits) : Bool × ℤ × ℤ :=
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  let sign := if sign == 1 then true else false
  let exponent := exponent.toNat
  let significand := significand.toNat
  (sign, exponent, significand)

def isExponentAllOnes (b : FloatBits) : Prop := b.toBitsTriple.exponent = BitVec.allOnes FloatFormat.exponentBits
/-- The exponent being all ones means that it is equivalent to 2^W - 1 -/
def isExponentAllOnes_eq_ofNat (b : FloatBits) : b.isExponentAllOnes ↔ b.toBitsTriple.exponent.toNat = (2^FloatFormat.exponentBits - 1) := by
  unfold isExponentAllOnes
  unfold BitVec.allOnes BitVec.toNat
  constructor
  · intro h
    rw [h]
    simp only [BitVec.val_toFin, BitVec.toNat_ofNatLt]
  · intro h
    ext
    rw [BitVec.val_toFin] at h
    simp only [BitVec.getLsb, h, Nat.testBit_two_pow_sub_one, Fin.is_lt, decide_True,
      BitVec.toNat_ofNatLt]



@[reducible]
def isTSignificandZero (b : FloatBits) : Prop := b.toBitsTriple.significand = 0

def isNaN (b : FloatBits) : Prop := b.isExponentAllOnes ∧ ¬b.isTSignificandZero
-- TODO qNaN vs sNaN

def isInfinite (b : FloatBits) : Prop := b.isExponentAllOnes ∧ b.isTSignificandZero

/-- Constructing a `FloatBitsTriple` from a `FloatBits` made by `(s, E, T)` will yield the same `(s, E, T)` -/
theorem construct_triple_eq_BitsTriple (hr : FloatFormat.radix = Radix.Binary) (s : BitVec FloatFormat.signBits) (E : BitVec FloatFormat.exponentBits) (T : BitVec FloatFormat.significandBits) :
  (FloatBits.mk' s E T).toBitsTriple.sign = s ∧ (FloatBits.mk' s E T).toBitsTriple.exponent = E ∧ (FloatBits.mk' s E T).toBitsTriple.significand = T := by
  unfold FloatBits.mk' FloatBits.toBitsTriple
  simp only [hr, beq_self_eq_true, ↓reduceDIte, eq_mpr_eq_cast, id_eq]
  simp_rw [FloatFormat.bitSize_eq_binary hr]
  unfold FloatFormat.signBits
  -- Is there no way to use omega to simplify?
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - FloatFormat.exponentBits - 1 = FloatFormat.significandBits by omega]
  rw [show 1 + FloatFormat.exponentBits + FloatFormat.significandBits - 1 = FloatFormat.significandBits + FloatFormat.exponentBits by omega]

  have kh : 1 + FloatFormat.exponentBits + FloatFormat.significandBits = FloatFormat.bitSize := by
    unfold FloatFormat.bitSize
    simp only [hr, ↓reduceIte]

  -- Simplify the casts out
  have kS := BitVec.extractLsb'_cast kh (FloatFormat.significandBits + FloatFormat.exponentBits) FloatFormat.signBits (s ++ E ++ T)
  have kE := BitVec.extractLsb'_cast kh FloatFormat.significandBits FloatFormat.exponentBits (s ++ E ++ T)
  have kT := BitVec.extractLsb'_cast kh 0 FloatFormat.significandBits (s ++ E ++ T)
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
  simp only [hr, ↓reduceIte, BitVec.ofNat_eq_ofNat]
  constructor
  · rw [construct_exponent_eq_BitsTriple hr]
  · rw [construct_significand_eq_BitsTriple hr]

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
  simp only [hr, ↓reduceIte, ne_eq, BitVec.ofNat_eq_ofNat]
  constructor
  · rw [construct_exponent_eq_BitsTriple hr]
  · rw [construct_significand_eq_BitsTriple hr]
    simp_all only [BitVec.ofNat_eq_ofNat, ne_eq, not_false_eq_true]

end FloatBits

instance [FloatFormat] {f : FloatBits} : Decidable f.isNaN := by
  unfold FloatBits.isNaN FloatBits.isExponentAllOnes
  infer_instance

-- TODO: For NaNs we really should be using a Quotient over the bit representations
-- def NaNFloatBits [F : FloatFormat] (b : Bool) : BitVec FloatFormat.bitSize := by

-- def NaNEquivalence [FloatFormat] (x y : FloatBits) : Prop := x.isNaN ∧ y.isNaN

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
      | inl h_1 =>
        subst h_1
        simp_all only [and_self, true_or]
      | inr h_2 => simp_all only [and_self, or_true]
    trans := by
      unfold FpEquiv
      intro x y z h1 h2
      cases h1 with
      | inl h =>
        cases h2 with
        | inl h_1 =>
          subst h h_1
          simp_all only [and_self, true_or]
        | inr h_2 =>
          subst h
          simp_all only [and_self, or_true]
      | inr h_1 =>
        cases h2 with
        | inl h =>
          subst h
          simp_all only [and_self, or_true]
        | inr h_2 => simp_all only [and_true, and_self, or_true]
  }

def FpQuotient [FloatFormat] : Type := Quotient FpSetoid

-- TODO: it may be possible to have a general way to turn a proof that applies to `Fp` and make it apply to `FpQuotient`..

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

noncomputable
def FpQuotient.choose [FloatFormat] (f : FpQuotient) : FloatBits :=
  @Quotient.out _ FpSetoid f

/-! Get a concrete bit pattern for the float, using a fixed representation for NaN values. -/
def FpQuotient.representative [FloatFormat] (f : FpQuotient) : FloatBits :=
  if f.isNaN then
    -- TODO: Make sure this isn't a signaling NaN
    have nz : BitVec.allOnes FloatFormat.significandBits ≠ 0 := by
      unfold FloatFormat.significandBits
      simp only [BitVec.ofNat_eq_ofNat, ne_eq]
      apply BitVec.allOnes_ne_zero
      have h := FloatFormat.valid_prec
      omega
    FloatBits.NaN false (BitVec.allOnes FloatFormat.significandBits) nz
  else
    sorry

-- TODO: We should hopefully be able to use the bitvec representation with the solver integrated into lean, but I need to look into that more.
def toBits [FloatFormat] (f : Fp) : FpQuotient := by
  -- unfold FloatFormat.bitSize FloatFormat.signBits
  -- if hr: FloatFormat.radix == Radix.Binary then
  --   simp only [LawfulBEq.eq_of_beq hr, ↓reduceIte]
  match f with
  | .finite f => sorry
  | .infinite b =>
    exact ⟦FloatBits.infinite b⟧
  | .NaN => sorry
  -- else
  --   exact BitVec.ofNat FloatFormat.bitSize 0

/-! Convert Bits back into a float.-/
def ofBits [FloatFormat] (b : FloatBits) : Fp := by
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  sorry



-- TODO: proof that we can convert bitsFloatTriple back to bits

-- TODO: have proofs that these are approximately inverses (except for NaN)
-- we can have subproofs for each of finite/infinite/nan



end Fp
