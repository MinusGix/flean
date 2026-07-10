import Flean.Operations.ModAddClock
import Flean.Operations.FpMatVec

/-! # A floating-point Fourier clock for modular addition

`ModAddClock.lean` specifies the ideal score directly as a sum of phase alignments.  This file gives
that specification the shape used by an ML implementation:

* a finite bank of frequencies, indexed by `Fin n`;
* a `2n`-dimensional cosine/sine feature vector;
* a readout matrix whose row for class `c` is the feature vector of `c`;
* a floating-point matrix-vector result, supplied by `FpMatVecBound`;
* an end-to-end error bound against the ideal `clockLogit` which separates table/feature
  quantization from dot-product arithmetic.

The file deliberately does not prescribe how the floating-point feature table is produced.  It may
be a rounded analytic Fourier table, the output of an earlier floating-point subnetwork, or weights
loaded from a trained model.  Its approximation error is explicit data, so all three uses share the
same downstream correctness theorem.
-/

set_option autoImplicit false

namespace Flean.ModAddClock

open Real Finset BigOperators

variable {p n : ℕ}

/-- A tensor-friendly, duplicate-free bank of nonzero Fourier frequencies. -/
structure FrequencyBank (p n : ℕ) where
  freq : Fin n → ZMod p
  injective_freq : Function.Injective freq
  freq_ne_zero : ∀ i, freq i ≠ 0

namespace FrequencyBank

/-- The `Finset` view used by the ideal clock specification. -/
def toFinset (B : FrequencyBank p n) : Finset (ZMod p) :=
  Finset.univ.image B.freq

@[simp] theorem mem_toFinset (B : FrequencyBank p n) (k : ZMod p) :
    k ∈ B.toFinset ↔ ∃ i, B.freq i = k := by
  simp [toFinset]

@[simp] theorem card_toFinset (B : FrequencyBank p n) : B.toFinset.card = n := by
  rw [toFinset, Finset.card_image_iff.mpr]
  · simp
  · exact B.injective_freq.injOn

theorem zero_notMem_toFinset (B : FrequencyBank p n) : (0 : ZMod p) ∉ B.toFinset := by
  simp [B.freq_ne_zero]

/-- The canonical real Fourier feature vector: first all cosine coordinates, then all sine
coordinates. -/
noncomputable def feature (B : FrequencyBank p n) (x : ZMod p) : Fin (n + n) → ℝ :=
  Fin.append (fun i => Real.cos (phase (B.freq i) x))
    (fun i => Real.sin (phase (B.freq i) x))

/-- The ideal readout row for candidate class `c`. -/
noncomputable def readoutRow (B : FrequencyBank p n) (c : ZMod p) : Fin (n + n) → ℝ :=
  B.feature c

end FrequencyBank

variable [hp : Fact p.Prime]

/-- Canonical phases respect subtraction modulo `p` after applying cosine.  Their real-valued
representatives may differ by an integer multiple of `2π`; cosine removes that choice of lift. -/
theorem cos_phase_sub (k s c : ZMod p) :
    Real.cos (phase k (s - c)) = Real.cos (phase k s - phase k c) := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  let A : ℤ := (k * s).val
  let C : ℤ := (k * c).val
  let D : ℤ := (k * (s - c)).val
  have hdvd : (p : ℤ) ∣ A - C - D := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [A, C, D, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  obtain ⟨q, hq⟩ := hdvd
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hqR : (A : ℝ) - C - D = p * q := by exact_mod_cast hq
  have hphase : phase k s - phase k c = phase k (s - c) + (q : ℝ) * (2 * π) := by
    unfold phase
    change 2 * π * (A : ℝ) / p - 2 * π * (C : ℝ) / p =
      2 * π * (D : ℝ) / p + (q : ℝ) * (2 * π)
    field_simp
    nlinarith [Real.pi_pos]
  rw [hphase, Real.cos_add_int_mul_two_pi]

/-- **Fourier tensor identity.** The dot product of the true-sum feature vector with candidate
class `c` is exactly the ideal clock logit.  This is the bridge from the phase-sum specification to
the matrix-vector operation implemented by an ML readout. -/
theorem feature_dot_eq_clockLogit (B : FrequencyBank p n) (s c : ZMod p) :
    (∑ j, B.feature s j * B.readoutRow c j) = clockLogit B.toFinset s c := by
  rw [Fin.sum_univ_add]
  simp only [FrequencyBank.feature, FrequencyBank.readoutRow, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i, (Real.cos (phase (B.freq i) s) * Real.cos (phase (B.freq i) c) +
        Real.sin (phase (B.freq i) s) * Real.sin (phase (B.freq i) c))) =
        ∑ i, Real.cos (phase (B.freq i) (s - c)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [cos_phase_sub, Real.cos_sub]
    _ = clockLogit B.toFinset s c := by
      rw [clockLogit, FrequencyBank.toFinset, Finset.sum_image]
      exact B.injective_freq.injOn

/-! ## Floating-point tables and matrix-vector execution -/

variable [FloatFormat]

omit hp [FloatFormat] in
/-- Every ideal Fourier coordinate has magnitude at most one. -/
theorem FrequencyBank.abs_feature_le_one (B : FrequencyBank p n) (x : ZMod p)
    (j : Fin (n + n)) : |B.feature x j| ≤ 1 := by
  unfold FrequencyBank.feature
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    exact abs_cos_le_one _
  · rw [Fin.append_right]
    exact abs_sin_le_one _

/-- Stored floating-point Fourier data.  Input features and readout rows are kept separate because
an actual network may compute the former and learn the latter by different routes.  The two error
fields are uniform coordinate-wise absolute bounds for each residue/class. -/
structure FpClockTables (B : FrequencyBank p n) where
  input : ZMod p → Fin (n + n) → FiniteFp
  readout : ZMod p → Fin (n + n) → FiniteFp
  inputErr : ZMod p → ℝ
  readoutErr : ZMod p → ℝ
  inputErr_nonneg : ∀ x, 0 ≤ inputErr x
  readoutErr_nonneg : ∀ c, 0 ≤ readoutErr c
  input_close : ∀ x j, |((input x j).toVal : ℝ) - B.feature x j| ≤ inputErr x
  readout_close : ∀ c j, |((readout c j).toVal : ℝ) - B.readoutRow c j| ≤ readoutErr c

namespace FpClockTables

variable {B : FrequencyBank p n}

/-- Readout rows arranged as the matrix expected by `FpMatVecBound`; `Fin p` is the tensor index
corresponding to a class in `ZMod p`. -/
def matrix (T : FpClockTables B) (i : Fin p) : Fin (n + n) → FiniteFp :=
  T.readout (i : ZMod p)

end FpClockTables

/-- Turn a residue into its canonical tensor row index. -/
def classIndex (c : ZMod p) : Fin p := ⟨c.val, ZMod.val_lt c⟩

omit [FloatFormat] in
@[simp] theorem classIndex_cast (c : ZMod p) : ((classIndex c : ℕ) : ZMod p) = c := by
  exact ZMod.natCast_zmod_val c

/-- A completed floating-point readout for every possible sum feature.  The matrix-vector bound
records the actual finite result and the arithmetic error of the chosen accumulation algorithm. -/
structure FpClockExecution (B : FrequencyBank p n) (T : FpClockTables B) where
  mv : ∀ s : ZMod p, FpMatVec.FpMatVecBound T.matrix (T.input s) ℝ

namespace FpClockExecution

variable {B : FrequencyBank p n} {T : FpClockTables B}

/-- The real value represented by the computed floating-point logit. -/
noncomputable def logit (E : FpClockExecution B T) (s c : ZMod p) : ℝ :=
  ((E.mv s).result (classIndex c)).toVal

/-- The arithmetic part of the logit error, directly from `FpMatVecBound`. -/
noncomputable def arithmeticError (E : FpClockExecution B T) (s c : ZMod p) : ℝ :=
  (E.mv s).relErr *
    ∑ j, |((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)|

/-- The table/feature part of the logit error.  There are `2n` coordinates; on each one,
`|r̃x̃-rx| ≤ εᵣ(1+εₓ)+εₓ` because both exact Fourier coordinates have magnitude at most one. -/
noncomputable def quantizationError (_E : FpClockExecution B T) (s c : ZMod p) : ℝ :=
  ((n + n : ℕ) : ℝ) *
    (T.readoutErr c * (1 + T.inputErr s) + T.inputErr s)

/-- Total certified per-logit error, split into arithmetic and table/feature components. -/
noncomputable def error (E : FpClockExecution B T) (s c : ZMod p) : ℝ :=
  E.arithmeticError s c + E.quantizationError s c

omit [FloatFormat] in
private theorem abs_stored_le_one_add_error {ideal stored err : ℝ}
    (hideal : |ideal| ≤ 1) (hclose : |stored - ideal| ≤ err) :
    |stored| ≤ 1 + err := by
  have h := abs_sub_abs_le_abs_sub stored ideal
  linarith

omit [FloatFormat] in
private theorem abs_mul_sub_mul_le {r x r₀ x₀ εr εx : ℝ}
    (hεr : 0 ≤ εr) (hεx : 0 ≤ εx)
    (hr₀ : |r₀| ≤ 1) (hx₀ : |x₀| ≤ 1)
    (hr : |r - r₀| ≤ εr) (hx : |x - x₀| ≤ εx) :
    |r * x - r₀ * x₀| ≤ εr * (1 + εx) + εx := by
  have hx_stored : |x| ≤ 1 + εx := abs_stored_le_one_add_error hx₀ hx
  have hεx_one : 0 ≤ 1 + εx := by linarith
  calc
    |r * x - r₀ * x₀| = |(r - r₀) * x + r₀ * (x - x₀)| := by ring_nf
    _ ≤ |(r - r₀) * x| + |r₀ * (x - x₀)| := abs_add_le _ _
    _ = |r - r₀| * |x| + |r₀| * |x - x₀| := by rw [abs_mul, abs_mul]
    _ ≤ εr * (1 + εx) + 1 * εx := by
      gcongr
    _ = εr * (1 + εx) + εx := by ring

/-- The stored-table dot product is close to the exact Fourier dot product, independently of how
the subsequent floating-point accumulation is performed. -/
theorem stored_dot_error_le (E : FpClockExecution B T) (s c : ZMod p) :
    |(∑ j, ((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)) -
        ∑ j, B.readoutRow c j * B.feature s j| ≤ E.quantizationError s c := by
  have hterm : ∀ j : Fin (n + n),
      |((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ) -
          B.readoutRow c j * B.feature s j| ≤
        T.readoutErr c * (1 + T.inputErr s) + T.inputErr s := by
    intro j
    exact abs_mul_sub_mul_le (T.readoutErr_nonneg c) (T.inputErr_nonneg s)
      (B.abs_feature_le_one c j) (B.abs_feature_le_one s j)
      (T.readout_close c j) (T.input_close s j)
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j, (((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ) -
        B.readoutRow c j * B.feature s j)| ≤
        ∑ j, |((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ) -
          B.readoutRow c j * B.feature s j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (n + n),
        (T.readoutErr c * (1 + T.inputErr s) + T.inputErr s) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = E.quantizationError s c := by
      rw [quantizationError, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- **End-to-end floating-point logit bound.**  The computed finite logit differs from the ideal
clock logit by at most `arithmeticError + quantizationError`. -/
theorem logit_error_le (E : FpClockExecution B T) (s c : ZMod p) :
    |E.logit s c - clockLogit B.toFinset s c| ≤ E.error s c := by
  have harith := (E.mv s).h_bound (classIndex c)
  simp only [FpClockTables.matrix, classIndex_cast] at harith
  have hquant := E.stored_dot_error_le s c
  have hideal : (∑ j, B.readoutRow c j * B.feature s j) = clockLogit B.toFinset s c := by
    calc
      (∑ j, B.readoutRow c j * B.feature s j) =
          ∑ j, B.feature s j * B.readoutRow c j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [mul_comm]
      _ = clockLogit B.toFinset s c := feature_dot_eq_clockLogit B s c
  rw [hideal] at hquant
  calc
    |E.logit s c - clockLogit B.toFinset s c| ≤
        |E.logit s c - ∑ j, ((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)| +
        |(∑ j, ((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)) -
          clockLogit B.toFinset s c| := by
            calc
              |E.logit s c - clockLogit B.toFinset s c| =
                  |(E.logit s c -
                      ∑ j, ((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)) +
                    ((∑ j, ((T.readout c j).toVal : ℝ) * ((T.input s j).toVal : ℝ)) -
                      clockLogit B.toFinset s c)| := by ring
              _ ≤ _ := abs_add_le _ _
    _ ≤ E.arithmeticError s c + E.quantizationError s c := add_le_add harith hquant
    _ = E.error s c := rfl

/-- The floating-point clock decodes `s` whenever every competitor's combined pointwise error fits
inside the ideal margin. -/
theorem correct_of_error_lt_margin (E : FpClockExecution B T) (s : ZMod p)
    (hmargin : ∀ c, c ≠ s → E.error s c + E.error s s < margin B.toFinset s) :
    ∀ c, c ≠ s → E.logit s c < E.logit s s :=
  correct_under_pointwise_perturbation B.toFinset s (E.logit s) (E.error s)
    (E.logit_error_le s) hmargin

/-- A transcendental-free sufficient condition for correct decoding.  The right side is the
algebraic redundancy threshold `8n/p²`, obtained from `eight_card_div_sq_le_margin`. -/
theorem correct_of_error_lt_eight_mul_card_div_sq (E : FpClockExecution B T) (s : ZMod p)
    (herror : ∀ c, c ≠ s →
      E.error s c + E.error s s < (8 : ℝ) * n / (p : ℝ) ^ 2) :
    ∀ c, c ≠ s → E.logit s c < E.logit s s := by
  apply E.correct_of_error_lt_margin s
  intro c hc
  have hm := eight_card_div_sq_le_margin B.toFinset B.zero_notMem_toFinset s
  rw [B.card_toFinset] at hm
  exact (herror c hc).trans_le hm

/-- Logits of the modular-addition decoder on an input pair. -/
noncomputable def decoderLogit (E : FpClockExecution B T)
    (a b c : ZMod p) : ℝ := E.logit (a + b) c

/-- The certified bad-input set for the actual floating-point realization.  Unlike the ideal
translation-invariant margin, the error is allowed to vary with both the input sum and candidate
class. -/
def CertifiedBadInputs (E : FpClockExecution B T) : Set (ZMod p × ZMod p) :=
  {ab | ∃ c, c ≠ ab.1 + ab.2 ∧
    margin B.toFinset (ab.1 + ab.2) ≤
      E.error (ab.1 + ab.2) c + E.error (ab.1 + ab.2) (ab.1 + ab.2)}

/-- A computable-shape over-approximation of the bad inputs, using only the rational/algebraic
threshold `8n/p²` rather than the exact trigonometric margin. -/
def AlgebraicBadInputs (E : FpClockExecution B T) : Set (ZMod p × ZMod p) :=
  {ab | ∃ c, c ≠ ab.1 + ab.2 ∧
    (8 : ℝ) * n / (p : ℝ) ^ 2 ≤
      E.error (ab.1 + ab.2) c + E.error (ab.1 + ab.2) (ab.1 + ab.2)}

/-- Any actual decoding failure lies in the explicitly certified bad-input set. -/
theorem failureSet_subset_certifiedBadInputs (E : FpClockExecution B T) :
    FailureSet E.decoderLogit ⊆ E.CertifiedBadInputs := by
  rintro ⟨a, b⟩ hab
  simp only [FailureSet, Set.mem_setOf_eq, decoderLogit] at hab
  simp only [CertifiedBadInputs, Set.mem_setOf_eq]
  push_neg at hab
  obtain ⟨c, hc, hfail⟩ := hab
  refine ⟨c, hc, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hcmem : c ∈ Finset.univ.erase (a + b) :=
    Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩
  have hsup : clockLogit B.toFinset (a + b) c ≤
      (Finset.univ.erase (a + b)).sup' (erase_univ_nonempty (a + b))
        (clockLogit B.toFinset (a + b)) := Finset.le_sup' _ hcmem
  have hideal : clockLogit B.toFinset (a + b) c ≤
      clockLogit B.toFinset (a + b) (a + b) - margin B.toFinset (a + b) := by
    rw [margin]
    linarith
  have hc_err := (abs_le.mp (E.logit_error_le (a + b) c)).2
  have hs_err := (abs_le.mp (E.logit_error_le (a + b) (a + b))).1
  have hcorrect : E.logit (a + b) c < E.logit (a + b) (a + b) := by
    linarith
  exact (not_lt_of_ge hfail) hcorrect

/-- Every actual decoding failure is also captured by the algebraic `8n/p²` threshold. -/
theorem failureSet_subset_algebraicBadInputs (E : FpClockExecution B T) :
    FailureSet E.decoderLogit ⊆ E.AlgebraicBadInputs := by
  intro ab hab
  obtain ⟨c, hc, hmargin⟩ := E.failureSet_subset_certifiedBadInputs hab
  refine ⟨c, hc, ?_⟩
  have hm := eight_card_div_sq_le_margin B.toFinset B.zero_notMem_toFinset (ab.1 + ab.2)
  rw [B.card_toFinset] at hm
  exact hm.trans hmargin

end FpClockExecution

end Flean.ModAddClock
