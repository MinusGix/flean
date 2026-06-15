import Flean.Operations.ScaledExact
import Flean.Rounding.RoundPreserves

/-! # Fixed-point arithmetic with bounded correction (the inexact frontier)

`ScaledExact` reduces float ops on common-scale values to *exact* integer arithmetic while
the result fits in `prec` bits. This file crosses into the **inexact** regime: when the
integer result needs renormalization, the float op equals the integer arithmetic **plus a
bounded correction**.

The correction is supplied by the generic round-error bound
`round_preserves_abs_error_unified` (in `Rounding/RoundPreserves.lean`), which holds for
**any nearest rounding mode** (`[RModeNearest R]` — both round-to-nearest-even and
round-to-nearest-away provide it) and needs *no* normal-range hypothesis (subnormals are
absorbed into the additive `2^(min_exp-prec)` tail). So these theorems are not policy-locked.

The reductionist reading: `fpOp a b = (integer op on the significands) · 2^scale + correction`
with `|correction| ≤ η·|value| + 2^(min_exp-prec)`. The integer arithmetic is *exact*; the
only loss is the bounded rounding correction — and where the result fits, the correction is
actually `0` (the `ScaledExact` lemmas). "Exact where it fits, bounded where it doesn't" is
exactly this pair.

NEXT: an inexact `ScaledInt` carrying an `err : R` field, composing these per-op corrections
across a computation (forward error in fixed-point coordinates).
-/

section ScaledCorrection

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Fixed-point addition with bounded correction.** For exact common-scale inputs
`a = m_a·2^s`, `b = m_b·2^s` with a finite result `f`, the float sum equals the integer sum
`(m_a + m_b)·2^s` up to a bounded correction. Exact when `m_a + m_b` fits in `prec` bits;
otherwise the renormalization correction is at most `η·|value| + 2^(min_exp-prec)`. -/
theorem fpAddFinite_scaled_correction (a b : FiniteFp) (m_a m_b s : ℤ) (f : FiniteFp)
    (ha : (a.toVal : R) = (m_a : R) * 2 ^ s) (hb : (b.toVal : R) = (m_b : R) * 2 ^ s)
    (hsum_nz : m_a + m_b ≠ 0)
    (hf : a + b = Fp.finite f) :
    |(f.toVal : R) - ((m_a + m_b : ℤ) : R) * 2 ^ s|
      ≤ η * |((m_a + m_b : ℤ) : R) * 2 ^ s|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by
    rw [ha, hb, ← add_mul]
    exact mul_ne_zero (by rw [← Int.cast_add]; exact_mod_cast hsum_nz) (by positivity)
  have hsum_eq : (a.toVal : R) + b.toVal = ((m_a + m_b : ℤ) : R) * 2 ^ s := by
    rw [ha, hb, ← add_mul]; push_cast; ring
  have hround : (○(((m_a + m_b : ℤ) : R) * 2 ^ s) : Fp) = Fp.finite f := by
    rw [← hsum_eq, ← fpAddFinite_correct (R := R) a b hsum_ne]; exact hf
  exact round_preserves_abs_error_unified (R := R) (((m_a + m_b : ℤ) : R) * 2 ^ s) hround

/-- **Fixed-point multiplication with bounded correction.** Scales add (`s_a + s_b`); the
float product equals the integer product `(m_a · m_b)·2^(s_a+s_b)` up to a bounded
correction `η·|value| + 2^(min_exp-prec)` (exact when `m_a · m_b` fits in `prec` bits). -/
theorem fpMulFinite_scaled_correction (a b : FiniteFp) (m_a m_b s_a s_b : ℤ) (f : FiniteFp)
    (ha : (a.toVal : R) = (m_a : R) * 2 ^ s_a) (hb : (b.toVal : R) = (m_b : R) * 2 ^ s_b)
    (hprod_nz : m_a * m_b ≠ 0)
    (hf : a * b = Fp.finite f) :
    |(f.toVal : R) - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
      ≤ η * |((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hprod_ne : (a.toVal : R) * b.toVal ≠ 0 := by
    rw [ha, hb]
    exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast left_ne_zero_of_mul hprod_nz) (by positivity))
      (mul_ne_zero (by exact_mod_cast right_ne_zero_of_mul hprod_nz) (by positivity))
  have hprod_eq : (a.toVal : R) * b.toVal = ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b) := by
    rw [ha, hb, zpow_add₀ (by norm_num : (2 : R) ≠ 0)]; push_cast; ring
  have hround : (○(((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)) : Fp) = Fp.finite f := by
    rw [← hprod_eq, ← fpMulFinite_correct (R := R) a b hprod_ne]; exact hf
  exact round_preserves_abs_error_unified (R := R)
    (((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)) hround

end ScaledCorrection
