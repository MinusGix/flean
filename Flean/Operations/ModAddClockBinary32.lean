import Flean.Operations.ModAddClockFp
import Flean.Rounding.RoundPreserves
import Flean.Rounding.PolicyInstances
import Flean.Operations.ExactIntAlgebra

/-! # Binary32 Fourier tables for the modular-addition clock

This file instantiates the abstract `FpClockTables` interface with actual IEEE Binary32 data.
Every table entry is the round-to-nearest, ties-to-even image of the corresponding exact cosine or
sine coordinate.  The construction is mathematical (`Real.sin`/`Real.cos` are noncomputable), but
the stored values are honest `FiniteFp` objects in the Binary32 format, not unconstrained witnesses.

The main objects are:

* `round` — Binary32 RNE rounding of a real in `[-1,1]`, extracted as a `FiniteFp`;
* `tables B` — rounded input and readout tables for any frequency bank `B`;
* `fullBank113` — all 112 nonzero frequencies for the standard prime modulus 113;
* `fullTables113` — its concrete `113 × 224` Binary32 cosine/sine tables.

The uniform coordinate error is

`tableError = 2⁻²⁴ + 2⁻¹⁵⁰`.

The first term is Binary32's half machine epsilon times the coordinate magnitude; the second is the
subnormal tail from `round_preserves_abs_error_unified`.  Since every Fourier coordinate has
magnitude at most one, this one constant certifies every entry.
-/

set_option autoImplicit false

namespace Flean.ModAddClock.Binary32

open Real

private local instance binary32Format : FloatFormat := FloatFormat.Binary32.toFloatFormat
private local instance nearestEvenPolicy : UseRoundingPolicy RoundNearestEvenPolicy := {}

/-- The exact Binary32 coordinate-wise error used for the tables. -/
noncomputable def tableError : ℝ := (2 : ℝ) ^ (-24 : ℤ) + (2 : ℝ) ^ (-150 : ℤ)

theorem tableError_nonneg : 0 ≤ tableError := by
  unfold tableError
  positivity

/-- Binary32's largest finite value is certainly at least one. -/
private theorem one_le_largestFiniteFloat :
    (1 : ℝ) ≤ FiniteFp.largestFiniteFloat.toVal := by
  rw [FiniteFp.largestFiniteFloat_toVal]
  change (1 : ℝ) ≤ 2 ^ (127 : ℤ) * (2 - 2 ^ (-23 : ℤ))
  norm_num

/-- RNE rounding in Binary32 is finite for every value in `[-1,1]`. -/
theorem round_isFinite (x : ℝ) (hx : |x| ≤ 1) : (○x : Fp).isFinite := by
  apply round_isFinite_of_abs_le_largest
  exact hx.trans one_le_largestFiniteFloat

/-- General finite-range form used by composed features and dot-product accumulation. -/
theorem round_isFinite_of_abs_le_largestFinite (x : ℝ)
    (hx : |x| ≤ FiniteFp.largestFiniteFloat.toVal) : (○x : Fp).isFinite :=
  round_isFinite_of_abs_le_largest x hx

/-- The actual finite Binary32 datum obtained by RNE rounding a real coordinate.  The fallback
branch of `toFiniteOr0` is unreachable under `|x| ≤ 1`; keeping the definition total makes it easy
to use as a table function. -/
noncomputable def round (x : ℝ) : FiniteFp := (○x : Fp).toFiniteOr0

/-- On the table domain, `round` really is the finite result of Binary32 RNE. -/
theorem round_eq (x : ℝ) (hx : |x| ≤ 1) : (○x : Fp) = Fp.finite (round x) :=
  Fp.eq_finite_toFiniteOr0 (round_isFinite x hx)

/-- `round` agrees with Binary32 RNE on any range known not to overflow. -/
theorem round_eq_of_abs_le_largestFinite (x : ℝ)
    (hx : |x| ≤ FiniteFp.largestFiniteFloat.toVal) :
    (○x : Fp) = Fp.finite (round x) :=
  Fp.eq_finite_toFiniteOr0 (round_isFinite_of_abs_le_largestFinite x hx)

/-- Unified Binary32 RNE error on any range known not to overflow. -/
theorem round_error_le_unified (x : ℝ)
    (hx : |x| ≤ FiniteFp.largestFiniteFloat.toVal) :
    |((round x).toVal : ℝ) - x| ≤
      (2 : ℝ) ^ (-24 : ℤ) * |x| + (2 : ℝ) ^ (-150 : ℤ) := by
  have h := round_preserves_abs_error_unified (R := ℝ) x
    (round_eq_of_abs_le_largestFinite x hx)
  simpa [FloatFormat.Binary32, StdFloatFormat.toFloatFormat, FloatFormat.hEps] using h

/-- Binary32 RNE error before replacing `|x|` by one. -/
theorem round_error_le (x : ℝ) (hx : |x| ≤ 1) :
    |((round x).toVal : ℝ) - x| ≤
      (2 : ℝ) ^ (-24 : ℤ) * |x| + (2 : ℝ) ^ (-150 : ℤ) := by
  exact round_error_le_unified x (hx.trans one_le_largestFiniteFloat)

/-- Uniform error for all sine/cosine coordinates in the Binary32 table. -/
theorem round_error_le_tableError (x : ℝ) (hx : |x| ≤ 1) :
    |((round x).toVal : ℝ) - x| ≤ tableError := by
  have h := round_error_le x hx
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-24 : ℤ) := by positivity
  unfold tableError
  nlinarith

/-- A single stored Binary32 coordinate of the Fourier table. -/
noncomputable def entry {p n : ℕ} (B : FrequencyBank p n) (x : ZMod p)
    (j : Fin (n + n)) : FiniteFp :=
  round (B.feature x j)

/-- Every stored coordinate is within `tableError` of the exact Fourier feature. -/
theorem entry_close {p n : ℕ} (B : FrequencyBank p n) (x : ZMod p) (j : Fin (n + n)) :
    |((entry B x j).toVal : ℝ) - B.feature x j| ≤ tableError :=
  round_error_le_tableError (B.feature x j) (B.abs_feature_le_one x j)

/-- Canonical Binary32 cosine/sine tables for a frequency bank.  Input and readout tables contain
the same rounded Fourier data; they remain separate fields in `FpClockTables` so a later learned
readout can replace one side without changing the execution/error interface. -/
noncomputable def tables {p n : ℕ} (B : FrequencyBank p n) : FpClockTables B where
  input := entry B
  readout := entry B
  inputErr := fun _ => tableError
  readoutErr := fun _ => tableError
  inputErr_nonneg := fun _ => tableError_nonneg
  readoutErr_nonneg := fun _ => tableError_nonneg
  input_close := entry_close B
  readout_close := by
    intro c j
    exact entry_close B c j

/-! ## The standard full bank for `p = 113` -/

private local instance prime113 : Fact (Nat.Prime 113) := ⟨by decide⟩

/-- Frequency `i` is the nonzero residue `i+1`, enumerating `1,…,112`. -/
def fullFrequency113 (i : Fin 112) : ZMod 113 := (i.val + 1 : ℕ)

@[simp] theorem fullFrequency113_val (i : Fin 112) :
    (fullFrequency113 i).val = i.val + 1 := by
  exact ZMod.val_natCast_of_lt (by omega)

/-- All nonzero frequencies for the prime modulus 113. -/
def fullBank113 : FrequencyBank 113 112 where
  freq := fullFrequency113
  injective_freq := by
    intro i j h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa using hv
  freq_ne_zero := by
    intro i h
    have hv := congrArg ZMod.val h
    simp at hv

/-- The full bank really is `ZMod 113 \ {0}`. -/
theorem fullBank113_toFinset : fullBank113.toFinset = Finset.univ.erase 0 := by
  ext k
  simp only [FrequencyBank.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨i, rfl⟩
    exact fullBank113.freq_ne_zero i
  · intro hk
    have hkpos : 0 < k.val := ZMod.val_pos.mpr hk
    have hklt : k.val < 113 := ZMod.val_lt k
    let i : Fin 112 := ⟨k.val - 1, by omega⟩
    refine ⟨i, ?_⟩
    apply ZMod.val_injective
    simp [fullBank113, i]
    omega

/-- The concrete full `p=113` Binary32 Fourier table: 113 residues, each with 224 coordinates
(112 cosines followed by 112 sines). -/
noncomputable def fullTables113 : FpClockTables fullBank113 := tables fullBank113

@[simp] theorem fullTables113_inputErr (x : ZMod 113) :
    fullTables113.inputErr x = tableError := rfl

@[simp] theorem fullTables113_readoutErr (c : ZMod 113) :
    fullTables113.readoutErr c = tableError := rfl

@[simp] theorem fullTables113_input (x : ZMod 113) (j : Fin 224) :
    fullTables113.input x j = entry fullBank113 x j := rfl

@[simp] theorem fullTables113_readout (c : ZMod 113) (j : Fin 224) :
    fullTables113.readout c j = entry fullBank113 c j := rfl

theorem fullTables113_input_close (x : ZMod 113) (j : Fin 224) :
    |((fullTables113.input x j).toVal : ℝ) - fullBank113.feature x j| ≤ tableError :=
  fullTables113.input_close x j

theorem fullTables113_readout_close (c : ZMod 113) (j : Fin 224) :
    |((fullTables113.readout c j).toVal : ℝ) - fullBank113.readoutRow c j| ≤ tableError :=
  fullTables113.readout_close c j

/-- Closed form of the table-quantization contribution for the full 224-coordinate readout. -/
theorem fullTables113_quantizationError
    (E : FpClockExecution fullBank113 fullTables113) (s c : ZMod 113) :
    E.quantizationError s c =
      (224 : ℝ) * (tableError * (1 + tableError) + tableError) := rfl

/-- Algebraic ideal-margin guarantee for the full 112-frequency bank at `p=113`. -/
theorem fullBank113_margin_lower (s : ZMod 113) :
    (896 : ℝ) / 12769 ≤ margin fullBank113.toFinset s := by
  have h := eight_card_div_sq_le_margin fullBank113.toFinset
    fullBank113.zero_notMem_toFinset s
  norm_num at h ⊢
  exact h

end Flean.ModAddClock.Binary32
