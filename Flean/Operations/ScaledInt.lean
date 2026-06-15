import Flean.Operations.ScaledCorrection

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
2^(min_exp-prec)`. Takes the (finite) result float `g` and the nonzero-sum witness. -/
def ScaledInt.add (a b : ScaledInt R) (g : FiniteFp) (hs : a.s = b.s)
    (hsum_ne : (a.fp.toVal : R) + b.fp.toVal ≠ 0)
    (hfin : a.fp + b.fp = Fp.finite g) : ScaledInt R where
  fp := g
  m := a.m + b.m
  s := a.s
  err := (1 + η) * (a.err + b.err) + η * |((a.m + b.m : ℤ) : R) * 2 ^ a.s|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb' : |(b.fp.toVal : R) - (b.m : R) * 2 ^ a.s| ≤ b.err := by rw [hs]; exact b.herr
    exact fpAddFinite_scaled_inexact a.fp b.fp a.m b.m a.s a.err b.err g a.herr hb'
      hsum_ne hfin

@[simp] theorem ScaledInt.add_m (a b : ScaledInt R) (g : FiniteFp) (hs hsum_ne hfin) :
    (a.add b g hs hsum_ne hfin).m = a.m + b.m := rfl
@[simp] theorem ScaledInt.add_s (a b : ScaledInt R) (g : FiniteFp) (hs hsum_ne hfin) :
    (a.add b g hs hsum_ne hfin).s = a.s := rfl
@[simp] theorem ScaledInt.add_fp (a b : ScaledInt R) (g : FiniteFp) (hs hsum_ne hfin) :
    (a.add b g hs hsum_ne hfin).fp = g := rfl

end Compose
