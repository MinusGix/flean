import Flean.IntegerEquivalence.SignBitOps
import Flean.Operations.Activation

/-! # FP ↔ Integer equivalence: ReLU as a sign-bit-driven masked select

Phase 3 of the FP ↔ Integer equivalence area.

`relu(x) = max(0, x)` for FP inputs is a single bit-level masked select:
return `+0` when the sign bit is set, otherwise return the input
unchanged. This is the most-cited single ML operation, and the
integer-pipeline implementation is one branch + one register copy.

* `FloatBits.bitRelu b := if b.sign then 0 else b` — bit-level operator.
* `Fp.fpRelu x := if x.sign then 0 else x` — Fp-level operator.
* `ofBits_bitRelu_eq_fpRelu` — bridge for non-NaN inputs.
* `fpRelu_toVal_eq_max` — connects the FP-level def to the standard
  math-level `max 0 x.toVal` for finite inputs (matches `Activation.relu`).

NaN handling: at `Fp` level, `Fp.NaN.sign = false` (def in `Defs.lean`),
so `fpRelu NaN = NaN` (passes through). At the bit level, NaN with
`sign = true` would be munged to `+0` by `bitRelu`, so the bridge takes
a non-NaN input hypothesis. Same carve-out shape as the rest of the
Phase 1/2 bridges.

Edge cases under non-NaN: `relu(-0) = +0` (bit-AND clears sign + the
zero-magnitude pattern stays zero — so `bitRelu` of any sign-true
finite zero is `+0`). `relu(-∞) = +0`. `relu(+∞) = +∞`. `relu(+0) = +0`.
All match the sign-bit-dispatch semantics. -/

namespace Fp.FloatBits

variable [FloatFormat]

/-- **Bit-level ReLU.** Returns `+0` if the sign bit is set, else the
input unchanged. -/
def bitRelu (b : FloatBits) : FloatBits :=
  if b.sign then 0 else b

@[simp] theorem bitRelu_pos (b : FloatBits) (hs : b.sign = false) :
    bitRelu b = b := by
  unfold bitRelu; rw [hs]; simp

@[simp] theorem bitRelu_neg (b : FloatBits) (hs : b.sign = true) :
    bitRelu b = 0 := by
  unfold bitRelu; rw [hs]; simp

theorem bitRelu_isFinite (b : FloatBits) (hf : b.isFinite) :
    (bitRelu b).isFinite := by
  unfold bitRelu
  by_cases hs : b.sign
  · rw [if_pos hs]
    -- Result is 0, which is finite.
    rw [zero_def']
    refine ⟨?_, ?_⟩
    · intro ⟨hE, _⟩
      unfold isExponentAllOnes at hE
      rw [construct_exponent_eq_BitsTriple] at hE
      have hpos := FloatFormat.exponentBits_pos
      have := BitVec.zero_ne_allOnes (by omega) hE
      contradiction
    · intro ⟨hE, _⟩
      unfold isExponentAllOnes at hE
      rw [construct_exponent_eq_BitsTriple] at hE
      have hpos := FloatFormat.exponentBits_pos
      have := BitVec.zero_ne_allOnes (by omega) hE
      contradiction
  · rw [if_neg hs]; exact hf

end Fp.FloatBits

namespace Fp

variable [FloatFormat]

/-- **Fp-level ReLU.** `relu x = if x.sign then 0 else x`.

For finite inputs this matches `max 0 x.toVal` (see `fpRelu_toVal_eq_max`).
For `NaN`, `Fp.NaN.sign = false`, so `fpRelu NaN = NaN` (passes through).
For `±∞`: `fpRelu (+∞) = +∞`, `fpRelu (-∞) = 0`. -/
def fpRelu (x : Fp) : Fp :=
  if x.sign then 0 else x

@[simp] theorem fpRelu_NaN : fpRelu (Fp.NaN : Fp) = Fp.NaN := rfl

@[simp] theorem fpRelu_pos (x : Fp) (hs : x.sign = false) : fpRelu x = x := by
  unfold fpRelu; rw [hs]; simp

@[simp] theorem fpRelu_neg (x : Fp) (hs : x.sign = true) : fpRelu x = 0 := by
  unfold fpRelu; rw [hs]; simp

end Fp

/-! ## Bit-level bridge -/

namespace Fp

/-- **Bit-level ReLU bridge.** For non-NaN bits, decoding the bit-level
ReLU equals the Fp-level ReLU on the decoded value. -/
theorem ofBits_bitRelu_eq_fpRelu [StdFloatFormat] (b : FloatBits)
    (hn : ¬b.isNaN) :
    ofBits (FloatBits.bitRelu b) = fpRelu (ofBits b) := by
  have h_sign : (ofBits b).sign = b.sign := ofBits_sign b hn
  unfold FloatBits.bitRelu fpRelu
  rw [h_sign]
  by_cases hs : b.sign
  · simp [hs]; exact ofBits_zero
  · simp [hs]

end Fp

/-! ## Math-level connection: `fpRelu x .toVal = max 0 x.toVal` -/

namespace Fp

variable [FloatFormat]

/-- `fpRelu` of a finite is always finite, and equal to `Fp.finite g` where
`g = if f.s then 0 else f` (the FiniteFp sign-dispatch form). -/
theorem fpRelu_finite_eq (f : FiniteFp) :
    fpRelu (Fp.finite f) = Fp.finite (if f.s then (0 : FiniteFp) else f) := by
  unfold fpRelu
  by_cases hs : f.s
  · have hsf : (Fp.finite f).sign = true := hs
    rw [if_pos hsf, if_pos hs]; rfl
  · have hsf : (Fp.finite f).sign = false := by
      show f.sign = false; rw [Bool.not_eq_true] at hs; exact hs
    rw [if_neg (by simp [hsf]), if_neg hs]

/-- For finite `x`, the FiniteFp under `fpRelu` has `toVal = max 0 x.toVal`
over any ordered field — matches the standard math-level `Activation.relu`. -/
theorem fpRelu_finite_inner_toVal {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (f : FiniteFp) :
    ((if f.s then (0 : FiniteFp) else f).toVal : R) = max 0 (f.toVal : R) := by
  by_cases hs : f.s
  · rw [if_pos hs]
    have h_neg_nonneg : (0 : R) ≤ ((-f).toVal : R) :=
      FiniteFp.toVal_nonneg (-f) (by rw [FiniteFp.neg_def]; simp [hs])
    rw [FiniteFp.toVal_neg_eq_neg] at h_neg_nonneg
    have h_nonpos : (f.toVal : R) ≤ 0 := by linarith
    rw [max_eq_left h_nonpos]
    show ((0 : FiniteFp).toVal : R) = (0 : R)
    exact FiniteFp.toVal_zero
  · rw [if_neg hs]
    rw [Bool.not_eq_true] at hs
    have h_nonneg : (0 : R) ≤ (f.toVal : R) := FiniteFp.toVal_nonneg f hs
    rw [max_eq_right h_nonneg]

end Fp

/-! ## Connection to math-level `Activation.relu`

`Flean.Activation.relu : Activation R` (in `Flean/Operations/Activation.lean`)
defines `relu(x) = max 0 x`. The lemma below confirms that the FP-level
`fpRelu` matches this on `toVal`-projected finite inputs. -/

open Flean

namespace Fp

variable [FloatFormat]

/-- For finite `f`, `(fpRelu (Fp.finite f))`'s `toVal` matches `Activation.relu`
applied to `f.toVal`. -/
theorem fpRelu_finite_eq_activation_relu {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : FiniteFp) :
    let g : FiniteFp := if f.s then 0 else f
    (g.toVal : R) = (Activation.relu (R := R)).apply (f.toVal : R) := by
  show ((if f.s then (0 : FiniteFp) else f).toVal : R)
        = max 0 (f.toVal : R)
  exact fpRelu_finite_inner_toVal f

end Fp

/-! ## Edge-case sanity theorems -/

namespace Fp

variable [FloatFormat]

/-- `relu(+0) = +0`. -/
@[simp] theorem fpRelu_zero : fpRelu (0 : Fp) = 0 := by
  unfold fpRelu
  show (if (0 : Fp).sign then (0 : Fp) else 0) = 0
  simp [Fp.sign, FiniteFp.zero_def]

/-- `relu(-0) = +0` (sign bit dispatches to zero output). -/
@[simp] theorem fpRelu_neg_zero : fpRelu (Fp.finite (-0 : FiniteFp)) = 0 := by
  unfold fpRelu
  show (if (Fp.finite (-(0 : FiniteFp))).sign then (0 : Fp)
          else Fp.finite (-(0 : FiniteFp))) = 0
  have hs : (Fp.finite (-(0 : FiniteFp))).sign = true := by
    show (-(0 : FiniteFp)).s = true
    rw [FiniteFp.neg_def]; rfl
  rw [if_pos hs]

/-- `relu(+∞) = +∞`. -/
@[simp] theorem fpRelu_pos_inf : fpRelu (Fp.infinite false) = Fp.infinite false := by
  unfold fpRelu
  show (if (Fp.infinite false).sign then (0 : Fp) else Fp.infinite false)
      = Fp.infinite false
  rfl

/-- `relu(-∞) = +0`. -/
@[simp] theorem fpRelu_neg_inf : fpRelu (Fp.infinite true) = 0 := by
  unfold fpRelu
  show (if (Fp.infinite true).sign then (0 : Fp) else Fp.infinite true) = 0
  rfl

end Fp
