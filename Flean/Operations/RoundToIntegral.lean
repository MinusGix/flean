import Flean.Operations.ExactInt

/-! # IEEE 754-2019 §5.9: Round to integral value

These operations round a floating-point operand to an integral value in the same format.

Five variants correspond to the five IEEE rounding directions:
- `roundToIntFloor` (toward negative infinity): `⌊x⌋`
- `roundToIntCeil` (toward positive infinity): `⌈x⌉`
- `roundToIntTrunc` (toward zero): truncation
- `roundToIntTiesToEven` (nearest, ties to even): default IEEE mode
- `roundToIntTiesToAway` (nearest, ties away from zero)

Special cases: NaN → NaN, ±∞ → ±∞, ±0 → ±0.
If the result is zero, the sign of the input is preserved (IEEE §5.9).
-/

section RoundToIntegral

variable [FloatFormat]

/-! ## Integer rounding functions

These are ℚ-specific integer rounding functions used by the roundToIntegral operations.
They live in a dedicated namespace to avoid polluting `Int`. -/

namespace IntRound

/-- Truncation toward zero: `⌊x⌋` for nonneg, `⌈x⌉` for neg. -/
def truncate (x : ℚ) : ℤ :=
  if 0 ≤ x then ⌊x⌋ else ⌈x⌉

/-- Round to nearest integer, ties to even. -/
def tiesToEven (x : ℚ) : ℤ :=
  let fr := Int.fract x
  if fr < 1 / 2 then ⌊x⌋
  else if 1 / 2 < fr then ⌈x⌉
  else if Even ⌊x⌋ then ⌊x⌋ else ⌈x⌉

/-- Round to nearest integer, ties away from zero. -/
def tiesAway (x : ℚ) : ℤ :=
  let fr := Int.fract x
  if fr < 1 / 2 then ⌊x⌋
  else if 1 / 2 < fr then ⌈x⌉
  else if 0 ≤ x then ⌈x⌉ else ⌊x⌋

theorem truncate_of_nonneg {x : ℚ} (hx : 0 ≤ x) : truncate x = ⌊x⌋ := by
  simp [truncate, hx]

theorem truncate_of_neg {x : ℚ} (hx : x < 0) : truncate x = ⌈x⌉ := by
  simp [truncate, not_le.mpr hx]

theorem truncate_int (n : ℤ) : truncate (n : ℚ) = n := by
  simp [truncate]

theorem tiesToEven_int (n : ℤ) : tiesToEven (n : ℚ) = n := by
  simp [tiesToEven, Int.fract_intCast]

theorem tiesAway_int (n : ℤ) : tiesAway (n : ℚ) = n := by
  simp [tiesAway, Int.fract_intCast]

end IntRound

/-! ## Core definition -/

/-- IEEE 754-2019 §5.9: Round to integral value in floating-point format.

Parameterized by an integer rounding function `intRound : ℚ → ℤ`.
For finite nonzero inputs, computes the integer rounding of the value,
then represents it as a float using `roundDown` (which is exact for
integers in the representable range). Zero results preserve the input sign. -/
def Fp.roundToInt (intRound : ℚ → ℤ) (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite b => .infinite b
  | .finite f =>
    if f.m = 0 then .finite f  -- ±0 preserved
    else
      let n := intRound (f.toVal : ℚ)
      if n = 0 then .finite (if f.s then -0 else 0)
      else roundDown ((n : ℚ))

/-! ## IEEE 754 §5.9 variants -/

/-- Round to integral toward negative infinity. -/
def Fp.roundToIntFloor : Fp → Fp := Fp.roundToInt (⌊·⌋)

/-- Round to integral toward positive infinity. -/
def Fp.roundToIntCeil : Fp → Fp := Fp.roundToInt (⌈·⌉)

/-- Round to integral toward zero (truncation). -/
def Fp.roundToIntTrunc : Fp → Fp := Fp.roundToInt IntRound.truncate

/-- Round to integral, ties to even (default IEEE rounding mode). -/
def Fp.roundToIntTiesToEven : Fp → Fp := Fp.roundToInt IntRound.tiesToEven

/-- Round to integral, ties away from zero. -/
def Fp.roundToIntTiesToAway : Fp → Fp := Fp.roundToInt IntRound.tiesAway

/-! ## Special cases -/

@[simp] theorem Fp.roundToInt_nan (intRound : ℚ → ℤ) :
    Fp.roundToInt intRound .NaN = .NaN := rfl

@[simp] theorem Fp.roundToInt_infinite (intRound : ℚ → ℤ) (b : Bool) :
    Fp.roundToInt intRound (.infinite b) = .infinite b := rfl

theorem Fp.roundToInt_zero (intRound : ℚ → ℤ) :
    Fp.roundToInt intRound (.finite (0 : FiniteFp)) = .finite 0 := by
  simp [Fp.roundToInt, FiniteFp.zero_def]

theorem Fp.roundToInt_neg_zero (intRound : ℚ → ℤ) :
    Fp.roundToInt intRound (.finite (-0 : FiniteFp)) = .finite (-0) := by
  simp [Fp.roundToInt, FiniteFp.neg_def, FiniteFp.zero_def]

/-- For finite nonzero inputs, `roundToInt` computes the integer rounding. -/
theorem Fp.roundToInt_finite_nonzero (intRound : ℚ → ℤ) (f : FiniteFp) (hm : f.m ≠ 0) :
    Fp.roundToInt intRound (.finite f) =
      let n := intRound (f.toVal : ℚ)
      if n = 0 then .finite (if f.s then -0 else 0)
      else roundDown ((n : ℚ)) := by
  simp [Fp.roundToInt, hm]

/-! ## Finiteness / exactness -/

/-- `roundToInt` always returns a finite float for finite inputs, provided the
integer rounding result is in the representable range. The hypothesis `h_bound` is
satisfied by all five IEEE rounding modes for any representable float. -/
theorem Fp.roundToInt_finite (intRound : ℚ → ℤ) (f : FiniteFp) (hm : f.m ≠ 0)
    (h_bound : (intRound (f.toVal : ℚ)).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ g : FiniteFp, Fp.roundToInt intRound (.finite f) = .finite g := by
  rw [Fp.roundToInt_finite_nonzero intRound f hm]
  set n := intRound (f.toVal : ℚ)
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    obtain ⟨g, hgm, hgv⟩ := int_representable (R := ℚ) n hn h_bound h_exp
    have hg_nnz : g.notNegZero := Or.inr hgm
    have hidem := roundDown_idempotent (R := ℚ) g hg_nnz
    rw [hgv] at hidem
    exact ⟨g, hidem⟩

/-- For integer-valued inputs with nonzero value, `roundToInt` with idempotent
rounding returns the original float. -/
theorem Fp.roundToInt_of_int_eq (intRound : ℚ → ℤ) (f : FiniteFp) (hm : f.m ≠ 0)
    (hnnz : f.notNegZero) (n : ℤ) (hn : (f.toVal : ℚ) = (n : ℚ))
    (hir : intRound (n : ℚ) = n) (hnn : n ≠ 0) :
    Fp.roundToInt intRound (.finite f) = .finite f := by
  rw [Fp.roundToInt_finite_nonzero intRound f hm]
  simp only [hn, hir, hnn, ↓reduceIte]
  have hidem := roundDown_idempotent (R := ℚ) f hnnz
  rw [hn] at hidem
  exact hidem

end RoundToIntegral
