import Flean.Operations.ModAddClockBinary32Literal

/-! # Packed literal Binary32 tensors

Bulk ingestion of real network weights as bit-exact Binary32 artifacts.  A `PackedMatrix r c T`
stores each matrix row as a single natural number (the little-endian concatenation of the row's
32-bit words), together with one boolean certificate checked by `decide`:

* every word decodes to a **finite** Binary32 value (no NaN or infinity), and
* every decoded magnitude is at most `2 ^ (T + min_exp - prec + 1)` (for Binary32,
  `2 ^ (T - 149)`).

The magnitude check is stated on the raw integral significand and exponent so the kernel only has
to compare natural numbers; `abs_toVal_le_of_checkWord` converts the certificate into the real
`|toVal|` bound used by forward-error analysis.  `PackedMatrix.value_toBits` shows ingestion is
bit-exact: each decoded entry re-encodes to the packed word.

This is the generic artifact-ingestion layer for the Nanda modular-addition checkpoint; the
generated weight files instantiate it.
-/

set_option autoImplicit false

namespace Flean.ModAddNanda

open Flean.ModAddClock.Binary32.Literal

private local instance binary32Std : StdFloatFormat := FloatFormat.Binary32

/-- Extract the `j`-th little-endian 32-bit word of a packed row. -/
def wordAt (data j : ℕ) : Word := BitVec.ofNat 32 (data >>> (32 * j))

/-- Fused per-word certificate: the word decodes to a finite Binary32 value whose integral
significand, shifted by its exponent's offset from `min_exp`, is at most `2 ^ T`.  This encodes
the magnitude bound `|toVal| ≤ 2 ^ (T + min_exp - prec + 1)` using only natural-number
arithmetic. -/
def checkWord (T : ℕ) (w : Word) : Bool :=
  if h : (bits w).isFinite then
    decide ((FiniteWord.mk w h).value.m *
      2 ^ ((FiniteWord.mk w h).value.e - FloatFormat.min_exp).toNat ≤ 2 ^ T)
  else false

theorem checkWord_isFinite {T : ℕ} {w : Word} (h : checkWord T w = true) :
    (bits w).isFinite := by
  by_contra hf
  rw [checkWord, dif_neg hf] at h
  exact Bool.false_ne_true h

theorem checkWord_le {T : ℕ} {w : Word} (h : checkWord T w = true)
    (hf : (bits w).isFinite) :
    (FiniteWord.mk w hf).value.m *
      2 ^ ((FiniteWord.mk w hf).value.e - FloatFormat.min_exp).toNat ≤ 2 ^ T := by
  rw [checkWord, dif_pos hf] at h
  exact of_decide_eq_true h

/-- The mathematical content of `checkWord`: a certified word's decoded value has magnitude at
most `2 ^ (T + min_exp - prec + 1)`. -/
theorem abs_toVal_le_of_checkWord {T : ℕ} {w : Word} (hf : (bits w).isFinite)
    (h : checkWord T w = true) :
    |((FiniteWord.mk w hf).value.toVal : ℝ)| ≤
      (2 : ℝ) ^ ((T : ℤ) + FloatFormat.min_exp - FloatFormat.prec + 1) := by
  set f := (FiniteWord.mk w hf).value with hfdef
  have hle := checkWord_le h hf
  have hmin : FloatFormat.min_exp ≤ f.e := f.valid_min_exp
  rw [← FiniteFp.toVal_mag_toVal_abs]
  unfold FiniteFp.toVal_mag
  have hradix : ((FloatFormat.radix.val : ℤ) : ℝ) = (2 : ℝ) := by norm_num [FloatFormat.radix, Radix.Binary]
  rw [hradix]
  have hsplit : f.e - FloatFormat.prec + 1 =
      ((f.e - FloatFormat.min_exp).toNat : ℤ) + (FloatFormat.min_exp - FloatFormat.prec + 1) := by
    omega
  rw [hsplit, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  have hcast : ((f.m : ℝ) * 2 ^ (f.e - FloatFormat.min_exp).toNat) ≤ (2 : ℝ) ^ T := by
    exact_mod_cast hle
  calc (f.m : ℝ) * ((2 : ℝ) ^ (f.e - FloatFormat.min_exp).toNat *
        (2 : ℝ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1))
      = ((f.m : ℝ) * 2 ^ (f.e - FloatFormat.min_exp).toNat) *
        (2 : ℝ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by ring
    _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by
        apply mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = (2 : ℝ) ^ ((T : ℤ) + FloatFormat.min_exp - FloatFormat.prec + 1) := by
        rw [← zpow_natCast (2 : ℝ) T, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring_nf

/-- Check every word of a packed row. -/
def checkRow (T c : ℕ) (data : ℕ) : Bool :=
  (List.range c).all fun j => checkWord T (wordAt data j)

/-- A matrix of Binary32 words, one packed natural per row, with a single decidable
finiteness-and-magnitude certificate. -/
structure PackedMatrix (r c T : ℕ) where
  rows : List ℕ
  hlen : rows.length = r
  hok : rows.all (checkRow T c) = true

namespace PackedMatrix

variable {r c T : ℕ} (M : PackedMatrix r c T)

/-- The packed `i`-th row. -/
def row (i : Fin r) : ℕ := M.rows[(i : ℕ)]'(by rw [M.hlen]; exact i.isLt)

theorem check_entry (i : Fin r) (j : Fin c) :
    checkWord T (wordAt (M.row i) (j : ℕ)) = true := by
  have hmem : M.row i ∈ M.rows := List.getElem_mem _
  have hrow := List.all_eq_true.mp M.hok _ hmem
  exact List.all_eq_true.mp hrow (j : ℕ) (List.mem_range.mpr j.isLt)

/-- The raw 32-bit word at position `(i, j)`. -/
def word (i : Fin r) (j : Fin c) : Word := wordAt (M.row i) (j : ℕ)

theorem word_isFinite (i : Fin r) (j : Fin c) : (bits (M.word i j)).isFinite :=
  checkWord_isFinite (M.check_entry i j)

/-- The certified finite literal at position `(i, j)`. -/
def entry (i : Fin r) (j : Fin c) : FiniteWord :=
  ⟨M.word i j, M.word_isFinite i j⟩

/-- The decoded Binary32 value at position `(i, j)`. -/
def value (i : Fin r) (j : Fin c) : FiniteFp := (M.entry i j).value

/-- Ingestion is bit-exact: every decoded entry re-encodes to its packed storage word. -/
theorem value_toBits (i : Fin r) (j : Fin c) :
    Fp.toBits (Fp.finite (M.value i j)) = ⟦bits (M.word i j)⟧ :=
  (M.entry i j).toBits_value

/-- The uniform magnitude bound carried by the packed certificate. -/
theorem abs_value_le (i : Fin r) (j : Fin c) :
    |((M.value i j).toVal : ℝ)| ≤
      (2 : ℝ) ^ ((T : ℤ) + FloatFormat.min_exp - FloatFormat.prec + 1) :=
  abs_toVal_le_of_checkWord (M.word_isFinite i j) (M.check_entry i j)

/-- Specialization with the bound exponent evaluated: for Binary32 a `PackedMatrix r c T`
certifies `|toVal| ≤ 2 ^ (T - 149)`, and the arithmetic side condition discharges by `decide`. -/
theorem abs_value_le' {r c T : ℕ} (M : PackedMatrix r c T) (t : ℤ)
    (ht : (T : ℤ) + FloatFormat.min_exp - FloatFormat.prec + 1 = t)
    (i : Fin r) (j : Fin c) :
    |((M.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ t :=
  ht ▸ M.abs_value_le i j

end PackedMatrix

end Flean.ModAddNanda
