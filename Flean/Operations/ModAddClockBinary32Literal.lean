import Flean.Encoding.Conversion
import Flean.Operations.ModAddClockBinary32

/-! # Literal Binary32 tables for the modular-addition clock

`ModAddClockBinary32.lean` defines table entries as canonical roundings of real trigonometric
coordinates.  Those values are mathematically precise, but noncomputable.  This file supplies the
other side of the boundary: finite Binary32 values backed by explicit 32-bit words.

The central separation is deliberate:

* `FiniteWord` checks that a word decodes to a finite Binary32 value and proves that re-encoding the
  value recovers the original word;
* `CertifiedVector` attaches a mathematical error certificate to a vector of such words;
* `LiteralClockTables.toFpClockTables` forgets only the literal packaging, producing the existing
  `FpClockTables` interface without any compatibility shim or additional numerical assumption.

The zero-residue row of the full `p = 113` bank is included as the first concrete certificate.  Its
112 cosine entries are the literal word `0x3f800000` and its 112 sine entries are `0x00000000`.
The full generated table can use exactly the same interface once interval certificates for the
nontrivial trigonometric entries are available.
-/

set_option autoImplicit false

namespace Flean.ModAddClock.Binary32.Literal

private local instance binary32Std : StdFloatFormat := FloatFormat.Binary32

/-- The storage word of an IEEE Binary32 value. -/
abbrev Word := BitVec 32

/-- Interpret a 32-bit word using Flean's Binary32 encoding. -/
def bits (word : Word) : Fp.FloatBits := ⟨word⟩

/-- A literal Binary32 word certified not to encode infinity or NaN. -/
structure FiniteWord where
  word : Word
  isFinite : (bits word).isFinite

namespace FiniteWord

/-- Decode a finite literal word to Flean's arithmetic representation. -/
def value (word : FiniteWord) : FiniteFp where
  s := (bits word.word).toBitsTriple.sign.toNat == 1
  e := (bits word.word).FpExponent
  m := (bits word.word).FpSignificand
  valid := Fp.FloatBits.isFinite_validFloatVal word.isFinite

/-- Decoding through the general IEEE decoder agrees with `FiniteWord.value`. -/
theorem ofBits_eq_finite (word : FiniteWord) :
    Fp.ofBits (bits word.word) = Fp.finite word.value := by
  simp only [Fp.ofBits]
  rw [dif_neg word.isFinite.1, dif_neg word.isFinite.2]
  rfl

/-- Re-encoding a decoded finite literal recovers its exact original 32 bits. -/
theorem toBits_value (word : FiniteWord) :
    Fp.toBits (Fp.finite word.value) = ⟦bits word.word⟧ := by
  rw [← word.ofBits_eq_finite, Fp.ofBits_toBits]

end FiniteWord

/-- The positive-zero Binary32 word. -/
def zero : FiniteWord := ⟨0x00000000, by decide⟩

/-- The Binary32 word for positive one. -/
def one : FiniteWord := ⟨0x3f800000, by decide⟩

@[simp] theorem zero_value : zero.value = 0 := by decide

@[simp] theorem one_value : one.value = 1 := by decide

/-- A literal vector together with a uniform absolute-error certificate against an ideal vector. -/
structure CertifiedVector {n : ℕ} (ideal : Fin n → ℝ) where
  entries : Fin n → FiniteWord
  error : ℝ
  error_nonneg : 0 ≤ error
  close : ∀ j, |(((entries j).value.toVal : ℝ)) - ideal j| ≤ error

namespace CertifiedVector

/-- The decoded finite-float vector underlying a literal certificate. -/
def values {n : ℕ} {ideal : Fin n → ℝ} (V : CertifiedVector ideal) : Fin n → FiniteFp :=
  fun j => (V.entries j).value

/-- Every decoded coordinate retains the exact word supplied by the literal vector. -/
theorem values_toBits {n : ℕ} {ideal : Fin n → ℝ} (V : CertifiedVector ideal) (j : Fin n) :
    Fp.toBits (Fp.finite (V.values j)) = ⟦bits (V.entries j).word⟧ :=
  (V.entries j).toBits_value

end CertifiedVector

/-- Fully literal input and readout tables, row-wise certified against a frequency bank. -/
structure LiteralClockTables {p n : ℕ} [Fact p.Prime] (B : FrequencyBank p n) where
  input : ∀ x, CertifiedVector (B.feature x)
  readout : ∀ c, CertifiedVector (B.readoutRow c)

namespace LiteralClockTables

/-- A certified literal table is directly usable by the existing floating-point clock API. -/
def toFpClockTables {p n : ℕ} [Fact p.Prime] {B : FrequencyBank p n}
    (T : LiteralClockTables B) : FpClockTables B where
  input := fun x => (T.input x).values
  readout := fun c => (T.readout c).values
  inputErr := fun x => (T.input x).error
  readoutErr := fun c => (T.readout c).error
  inputErr_nonneg := fun x => (T.input x).error_nonneg
  readoutErr_nonneg := fun c => (T.readout c).error_nonneg
  input_close := fun x => (T.input x).close
  readout_close := fun c => (T.readout c).close

/-- Input values exposed through `FpClockTables` re-encode to the supplied literal words. -/
theorem input_toBits {p n : ℕ} [Fact p.Prime] {B : FrequencyBank p n}
    (T : LiteralClockTables B) (x : ZMod p) (j : Fin (n + n)) :
    Fp.toBits (Fp.finite (T.toFpClockTables.input x j)) =
      ⟦bits ((T.input x).entries j).word⟧ :=
  (T.input x).values_toBits j

/-- Readout values exposed through `FpClockTables` re-encode to the supplied literal words. -/
theorem readout_toBits {p n : ℕ} [Fact p.Prime] {B : FrequencyBank p n}
    (T : LiteralClockTables B) (c : ZMod p) (j : Fin (n + n)) :
    Fp.toBits (Fp.finite (T.toFpClockTables.readout c j)) =
      ⟦bits ((T.readout c).entries j).word⟧ :=
  (T.readout c).values_toBits j

end LiteralClockTables

/-! ## First concrete row -/

private local instance prime113 : Fact (Nat.Prime 113) := ⟨by decide⟩

/-- Literal Binary32 words for the full-bank feature at residue zero. -/
def fullBank113ZeroWords : Fin 224 → FiniteWord :=
  Fin.append (fun _ : Fin 112 => one) (fun _ : Fin 112 => zero)

/-- The literal zero-residue row is exact: all cosine coordinates are one and all sine coordinates
are zero. -/
def fullBank113ZeroRow : CertifiedVector (fullBank113.feature 0) where
  entries := fullBank113ZeroWords
  error := 0
  error_nonneg := le_rfl
  close := by
    intro j
    unfold fullBank113ZeroWords FrequencyBank.feature
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left, Fin.append_left, one_value]
      simp [phase]
    · rw [Fin.append_right, Fin.append_right, zero_value]
      simp [phase]

/-- Every cosine word in the literal zero row is the IEEE encoding of one. -/
@[simp] theorem fullBank113ZeroRow_cos_word (i : Fin 112) :
    (fullBank113ZeroRow.entries (Fin.castAdd 112 i)).word = (0x3f800000 : Word) := by
  change (fullBank113ZeroWords (Fin.castAdd 112 i)).word = _
  unfold fullBank113ZeroWords
  rw [Fin.append_left]
  rfl

/-- Every sine word in the literal zero row is the IEEE encoding of zero. -/
@[simp] theorem fullBank113ZeroRow_sin_word (i : Fin 112) :
    (fullBank113ZeroRow.entries (Fin.natAdd 112 i)).word = (0x00000000 : Word) := by
  change (fullBank113ZeroWords (Fin.natAdd 112 i)).word = _
  unfold fullBank113ZeroWords
  rw [Fin.append_right]
  rfl

end Flean.ModAddClock.Binary32.Literal
