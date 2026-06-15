import Flean.Operations.ScaledCorrection
import Flean.Operations.ExactIntAlgebra

/-! # Inexact fixed-point values — composing corrections (forward error in scale coords)

`ScaledCorrection` bounds *one* float op against the integer arithmetic. This file composes
those per-op corrections across a computation: a `ScaledInt R` is a float `fp` together with
the ideal fixed-point value `m · 2^s` it is *meant* to represent and a running error bound
`err` with `|fp.toVal - m · 2^s| ≤ err`.

Operations accumulate error: adding two inexact values, the new error is the two input
errors plus the rounding correction of the actual float op (which, in turn, is bounded
against the *ideal* magnitude). This is forward error analysis carried in fixed-point
("integer × scale") coordinates — the reduction "this float computation = this integer
computation, to within `err`" extended from one op to a chain.

`ofExact` gives the `err = 0` base (a representable `m · 2^s`); each `add` grows it by the
closed form `(1+η)(err_a+err_b) + η|value| + 2^(min_exp-prec)`.
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float with the fixed-point value `m · 2^s` it approximates, and a bound `err` on the
deviation. `err = 0` is the exact (`ScaledExact`) case. -/
structure ScaledInt (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- Integer significand of the ideal fixed-point value. -/
  m : ℤ
  /-- Scale (ulp exponent) of the ideal fixed-point value. -/
  s : ℤ
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the ideal value `m · 2^s`. -/
  herr : |(fp.toVal : R) - (m : R) * 2 ^ s| ≤ err

/-- The ideal value `m · 2^s` this approximates. -/
def ScaledInt.value (a : ScaledInt R) : R := (a.m : R) * 2 ^ a.s

/-- The exact base case: a representable fixed-point value, with zero error. -/
def ScaledInt.ofExact (f : FiniteFp) (m s : ℤ) (h : (f.toVal : R) = (m : R) * 2 ^ s) :
    ScaledInt R :=
  ⟨f, m, s, 0, by rw [h]; simp⟩

@[simp] theorem ScaledInt.ofExact_err (f : FiniteFp) (m s : ℤ)
    (h : (f.toVal : R) = (m : R) * 2 ^ s) : (ScaledInt.ofExact f m s h).err = (0 : R) := rfl

section Compose

variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Composition building block.** Adding two *inexact* common-scale values: the deviation
of the float result from the ideal integer sum `(m_a + m_b)·2^s` is the two input errors
plus this op's rounding correction (bounded against the ideal magnitude). -/
theorem fpAddFinite_scaled_inexact (a b : FiniteFp) (m_a m_b s : ℤ) (err_a err_b : R)
    (f : FiniteFp)
    (ha : |(a.toVal : R) - (m_a : R) * 2 ^ s| ≤ err_a)
    (hb : |(b.toVal : R) - (m_b : R) * 2 ^ s| ≤ err_b)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hf : a + b = Fp.finite f) :
    |(f.toVal : R) - ((m_a + m_b : ℤ) : R) * 2 ^ s|
      ≤ (1 + η) * (err_a + err_b) + η * |((m_a + m_b : ℤ) : R) * 2 ^ s|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hη_nn : (0 : R) ≤ η := by positivity
  have hround : (○((a.toVal : R) + b.toVal) : Fp) = Fp.finite f := by
    rw [← fpAddFinite_correct (R := R) a b hsum_ne]; exact hf
  have hrb := round_preserves_abs_error_unified (R := R) ((a.toVal : R) + b.toVal) hround
  have hinput : |((a.toVal : R) + b.toVal) - ((m_a + m_b : ℤ) : R) * 2 ^ s| ≤ err_a + err_b := by
    have heq : ((a.toVal : R) + b.toVal) - ((m_a + m_b : ℤ) : R) * 2 ^ s
        = ((a.toVal : R) - (m_a : R) * 2 ^ s) + ((b.toVal : R) - (m_b : R) * 2 ^ s) := by
      push_cast; ring
    rw [heq]; exact (abs_add_le _ _).trans (add_le_add ha hb)
  have hmag : |(a.toVal : R) + b.toVal|
      ≤ |((m_a + m_b : ℤ) : R) * 2 ^ s| + (err_a + err_b) := by
    have h1 := abs_sub_abs_le_abs_sub ((a.toVal : R) + b.toVal)
      (((m_a + m_b : ℤ) : R) * 2 ^ s)
    linarith [hinput, h1]
  calc |(f.toVal : R) - ((m_a + m_b : ℤ) : R) * 2 ^ s|
      ≤ |(f.toVal : R) - ((a.toVal : R) + b.toVal)|
          + |((a.toVal : R) + b.toVal) - ((m_a + m_b : ℤ) : R) * 2 ^ s| := abs_sub_le _ _ _
    _ ≤ (η * |(a.toVal : R) + b.toVal|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)) + (err_a + err_b) :=
        add_le_add hrb hinput
    _ ≤ (η * (|((m_a + m_b : ℤ) : R) * 2 ^ s| + (err_a + err_b))
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)) + (err_a + err_b) := by
        gcongr
    _ = (1 + η) * (err_a + err_b) + η * |((m_a + m_b : ℤ) : R) * 2 ^ s|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

/-- **Inexact same-scale addition.** Errors compose: `err' = (1+η)(err_a+err_b) + η|value| +
2^(min_exp-prec)`. The result float is computed automatically (`toFiniteOr0`); the caller
supplies only that the sum is finite (no overflow) and nonzero. -/
def ScaledInt.add (a b : ScaledInt R) (hs : a.s = b.s)
    (hsum_ne : (a.fp.toVal : R) + b.fp.toVal ≠ 0)
    (hfin : (a.fp + b.fp).isFinite) : ScaledInt R where
  fp := (a.fp + b.fp).toFiniteOr0
  m := a.m + b.m
  s := a.s
  err := (1 + η) * (a.err + b.err) + η * |((a.m + b.m : ℤ) : R) * 2 ^ a.s|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb' : |(b.fp.toVal : R) - (b.m : R) * 2 ^ a.s| ≤ b.err := by rw [hs]; exact b.herr
    exact fpAddFinite_scaled_inexact a.fp b.fp a.m b.m a.s a.err b.err _ a.herr hb'
      hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)

@[simp] theorem ScaledInt.add_m (a b : ScaledInt R) (hs hsum_ne hfin) :
    (a.add b hs hsum_ne hfin).m = a.m + b.m := rfl
@[simp] theorem ScaledInt.add_s (a b : ScaledInt R) (hs hsum_ne hfin) :
    (a.add b hs hsum_ne hfin).s = a.s := rfl
@[simp] theorem ScaledInt.add_fp (a b : ScaledInt R) (hs hsum_ne hfin) :
    (a.add b hs hsum_ne hfin).fp = (a.fp + b.fp).toFiniteOr0 := rfl
@[simp] theorem ScaledInt.add_err (a b : ScaledInt R) (hs hsum_ne hfin) :
    (a.add b hs hsum_ne hfin).err
      = (1 + η) * (a.err + b.err) + η * |((a.m + b.m : ℤ) : R) * 2 ^ a.s|
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := rfl

/-- **Composition building block (multiplication).** Multiplying two inexact values: scales
add, and the deviation of the float result from the ideal product `(m_a·m_b)·2^(s_a+s_b)` is
the propagated input error `|ideal_a|·err_b + err_a·|ideal_b| + err_a·err_b` plus this op's
rounding correction. -/
theorem fpMulFinite_scaled_inexact (a b : FiniteFp) (m_a m_b s_a s_b : ℤ) (err_a err_b : R)
    (f : FiniteFp)
    (ha : |(a.toVal : R) - (m_a : R) * 2 ^ s_a| ≤ err_a)
    (hb : |(b.toVal : R) - (m_b : R) * 2 ^ s_b| ≤ err_b)
    (hprod_ne : (a.toVal : R) * b.toVal ≠ 0)
    (hf : a * b = Fp.finite f) :
    |(f.toVal : R) - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
      ≤ η * |((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
        + (1 + η) * (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b|
            + err_a * err_b)
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hη_nn : (0 : R) ≤ η := by positivity
  have herr_a_nn : (0 : R) ≤ err_a := le_trans (abs_nonneg _) ha
  have hround : (○((a.toVal : R) * b.toVal) : Fp) = Fp.finite f := by
    rw [← fpMulFinite_correct (R := R) a b hprod_ne]; exact hf
  have hrb := round_preserves_abs_error_unified (R := R) ((a.toVal : R) * b.toVal) hround
  have hval_eq : ((m_a : R) * 2 ^ s_a) * ((m_b : R) * 2 ^ s_b)
      = ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b) := by
    rw [zpow_add₀ (by norm_num : (2 : R) ≠ 0)]; push_cast; ring
  have hinput : |(a.toVal : R) * b.toVal - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
      ≤ |(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b| + err_a * err_b := by
    have hexp : (a.toVal : R) * b.toVal - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)
        = ((m_a : R) * 2 ^ s_a) * ((b.toVal : R) - (m_b : R) * 2 ^ s_b)
          + ((a.toVal : R) - (m_a : R) * 2 ^ s_a) * ((m_b : R) * 2 ^ s_b)
          + ((a.toVal : R) - (m_a : R) * 2 ^ s_a) * ((b.toVal : R) - (m_b : R) * 2 ^ s_b) := by
      rw [← hval_eq]; ring
    rw [hexp]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) herr_a_nn
  have hmag : |(a.toVal : R) * b.toVal|
      ≤ |((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
        + (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b| + err_a * err_b) := by
    have h1 := abs_sub_abs_le_abs_sub ((a.toVal : R) * b.toVal)
      (((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b))
    linarith [hinput, h1]
  calc |(f.toVal : R) - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
      ≤ |(f.toVal : R) - (a.toVal : R) * b.toVal|
          + |(a.toVal : R) * b.toVal - ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)| := abs_sub_le _ _ _
    _ ≤ (η * |(a.toVal : R) * b.toVal|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
        + (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b| + err_a * err_b) :=
        add_le_add hrb hinput
    _ ≤ (η * (|((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
            + (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b| + err_a * err_b))
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ))
        + (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b| + err_a * err_b) := by
        gcongr
    _ = η * |((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)|
        + (1 + η) * (|(m_a : R) * 2 ^ s_a| * err_b + err_a * |(m_b : R) * 2 ^ s_b|
            + err_a * err_b)
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

/-- **Inexact multiplication.** Scales add (`s_a + s_b`); errors compose with the product
propagation. Result float computed automatically; caller supplies finiteness + nonzero. -/
def ScaledInt.mul (a b : ScaledInt R)
    (hprod_ne : (a.fp.toVal : R) * b.fp.toVal ≠ 0)
    (hfin : (a.fp * b.fp).isFinite) : ScaledInt R where
  fp := (a.fp * b.fp).toFiniteOr0
  m := a.m * b.m
  s := a.s + b.s
  err := η * |((a.m * b.m : ℤ) : R) * 2 ^ (a.s + b.s)|
          + (1 + η) * (|(a.m : R) * 2 ^ a.s| * b.err + a.err * |(b.m : R) * 2 ^ b.s|
              + a.err * b.err)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := fpMulFinite_scaled_inexact a.fp b.fp a.m b.m a.s b.s a.err b.err _ a.herr b.herr
    hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)

@[simp] theorem ScaledInt.mul_m (a b : ScaledInt R) (hprod_ne hfin) :
    (a.mul b hprod_ne hfin).m = a.m * b.m := rfl
@[simp] theorem ScaledInt.mul_s (a b : ScaledInt R) (hprod_ne hfin) :
    (a.mul b hprod_ne hfin).s = a.s + b.s := rfl
@[simp] theorem ScaledInt.mul_fp (a b : ScaledInt R) (hprod_ne hfin) :
    (a.mul b hprod_ne hfin).fp = (a.fp * b.fp).toFiniteOr0 := rfl
@[simp] theorem ScaledInt.mul_err (a b : ScaledInt R) (hprod_ne hfin) :
    (a.mul b hprod_ne hfin).err
      = η * |((a.m * b.m : ℤ) : R) * 2 ^ (a.s + b.s)|
        + (1 + η) * (|(a.m : R) * 2 ^ a.s| * b.err + a.err * |(b.m : R) * 2 ^ b.s|
            + a.err * b.err)
        + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := rfl

end Compose

/-! ## Deriving finiteness from a magnitude bound

The `add`/`mul` ops above ask the caller for an `isFinite` Prop. These variants derive it
from a no-overflow magnitude bound (`|value| ≤ largestFiniteFloat`), via the generic
`round_isFinite_of_abs_le_largest` (in `Rounding/RoundPreserves.lean`), so callers who carry
a bound — which the running `err` already provides — need not establish finiteness directly.
-/

section BoundedOps

variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R] [RModeMono R] [RModeIdem R]

/-- `add` with finiteness derived from a no-overflow bound on the float sum. -/
def ScaledInt.addOfBound (a b : ScaledInt R) (hs : a.s = b.s)
    (hsum_ne : (a.fp.toVal : R) + b.fp.toVal ≠ 0)
    (hbnd : |(a.fp.toVal : R) + b.fp.toVal| ≤ FiniteFp.largestFiniteFloat.toVal (R := R)) :
    ScaledInt R :=
  a.add b hs hsum_ne (by
    have h := round_isFinite_of_abs_le_largest (R := R) ((a.fp.toVal : R) + b.fp.toVal) hbnd
    rwa [← fpAddFinite_correct (R := R) a.fp b.fp hsum_ne] at h)

/-- `mul` with finiteness derived from a no-overflow bound on the float product. -/
def ScaledInt.mulOfBound (a b : ScaledInt R)
    (hprod_ne : (a.fp.toVal : R) * b.fp.toVal ≠ 0)
    (hbnd : |(a.fp.toVal : R) * b.fp.toVal| ≤ FiniteFp.largestFiniteFloat.toVal (R := R)) :
    ScaledInt R :=
  a.mul b hprod_ne (by
    have h := round_isFinite_of_abs_le_largest (R := R) ((a.fp.toVal : R) * b.fp.toVal) hbnd
    rwa [← fpMulFinite_correct (R := R) a.fp b.fp hprod_ne] at h)

/-! ## Demo: error accumulates along a chain

Starting from three *exact* values (`err = 0`), a chain of two additions builds the error up
term by term. The closed form makes the accumulation visible: a `η·magnitude` term per op,
and the first op's rounding tail amplified by `(1+η)` when the second op consumes it. -/

omit [RModeMono R] [RModeIdem R] in
/-- Two chained additions on exact inputs: the running error, by `rfl`-level computation, is
`η(1+η)·|first sum| + η·|total| + (2+η)·2^(min_exp-prec)` — two rounding contributions, the
first amplified by `(1+η)`. (Compare the inputs' `err = 0`.) -/
theorem ScaledInt.chain_two_adds_err (a b c : ScaledInt R)
    (ha0 : a.err = 0) (hb0 : b.err = 0) (hc0 : c.err = 0)
    (hsab : a.s = b.s) (hsac : a.s = c.s)
    (hne1 : (a.fp.toVal : R) + b.fp.toVal ≠ 0)
    (hfin1 : (a.fp + b.fp).isFinite)
    (hne2 : ((a.add b hsab hne1 hfin1).fp.toVal : R) + c.fp.toVal ≠ 0)
    (hfin2 : ((a.add b hsab hne1 hfin1).fp + c.fp).isFinite) :
    ((a.add b hsab hne1 hfin1).add c hsac hne2 hfin2).err
      = η * (1 + η) * |((a.m + b.m : ℤ) : R) * 2 ^ a.s|
        + η * |((a.m + b.m + c.m : ℤ) : R) * 2 ^ a.s|
        + (2 + η) * (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  simp only [ScaledInt.add_err, ScaledInt.add_m, ScaledInt.add_s, ha0, hb0, hc0]
  ring

end BoundedOps
