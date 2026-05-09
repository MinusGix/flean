import Flean.IntegerEquivalence.LeakyReluBits
import Flean.Operations.LogBScaleB
import Flean.Operations.Sub

/-! # FP ↔ Integer equivalence: libm intrinsics

Phase 1.8 of the FP ↔ Integer equivalence area.

Surface the standard libm bit-twiddle functions under their canonical names,
each backed by a bit-level corollary. All functions are aliases or thin
wrappers over already-shipped operators — the value of this file is naming
parity with C99/IEEE 754, so downstream codegen and SIMD targeting can
recognize them.

* `Fp.signbit` — sign-bit extract.
* `Fp.ldexp` / `Fp.scalbn` / `Fp.scalbln` — multiply by `2^k`.
* `Fp.fdim` — `max(x - y, 0)`, composes `fpSub` with Phase 3 `fpRelu`.
* `FiniteFp.ilogb` — bit-level form of integer-valued `logB` on normal inputs.

`logb` and `scaleB` are already shipped at the value level in
`Operations/LogBScaleB.lean`; we add bit-level corollaries for the most-used
special cases. -/

namespace Fp

variable [FloatFormat]

/-! ## `signbit` — single bit extract -/

/-- **`signbit x : Bool`** — returns `true` iff `x` is negative-signed.
Aliases `Fp.sign`. The libm spec says `signbit(NaN)` is unspecified;
here it follows `Fp.sign` (= `false` for `Fp.NaN` per `Defs.lean`). -/
@[reducible] def signbit (x : Fp) : Bool := x.sign

end Fp

namespace Fp

/-- For non-NaN bits, `signbit` matches the bit-level sign. -/
theorem signbit_ofBits [StdFloatFormat] (b : FloatBits) (hn : ¬b.isNaN) :
    signbit (ofBits b) = b.sign := by
  unfold signbit
  exact ofBits_sign b hn

end Fp

/-! ## `ldexp` / `scalbn` / `scalbln` — multiply by `2^k`

All three libm functions have identical semantics in IEEE 754
(differing only in the type of the exponent argument in C). Implementation
is `fpMul x (pow2Float k)`. -/

namespace Fp

variable [FloatFormat]

/-- **`ldexp x k`** = `x · 2^k`. Equivalent to `fpMul x (pow2Float k)`
when `min_exp ≤ k ≤ max_exp`. -/
noncomputable def ldexp [RModeExec]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k)
    (hk_hi : k ≤ FloatFormat.max_exp)
    (x : Fp) : Fp :=
  fpMul x (Fp.finite (pow2Float k hk_lo hk_hi))

/-- **`scalbn x k`** — alias for `ldexp` (semantics-equal in IEEE 754). -/
noncomputable abbrev scalbn [RModeExec]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k)
    (hk_hi : k ≤ FloatFormat.max_exp)
    (x : Fp) : Fp :=
  ldexp k hk_lo hk_hi x

/-- **`scalbln x k`** — long-int version, identical to `ldexp` in our
integer-only formulation. -/
noncomputable abbrev scalbln [RModeExec]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ k)
    (hk_hi : k ≤ FloatFormat.max_exp)
    (x : Fp) : Fp :=
  ldexp k hk_lo hk_hi x

end Fp

namespace Fp

/-- **Bit-level form of `ldexp`** for bit-normal inputs with normal-range
result: `ldexp (ofBits b) k = ofBits (setBiasedExponent E_new b)` where
`E_new` is the bumped biased exponent. Composes
`ofBits_setBiasedExponent_eq_fpMul_pow2` from `MulPow2.lean`. -/
theorem ldexp_eq_ofBits_setBiasedExponent
    [StdFloatFormat] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (b : FloatBits) (k : ℤ) (E_new : BitVec FloatFormat.exponentBits)
    (hn_b : b.isNormal)
    (hE_nz : E_new ≠ 0)
    (hE_not_allOnes : E_new ≠ BitVec.allOnes FloatFormat.exponentBits)
    (hE_diff : (E_new.toNat : ℤ) = b.toBitsTriple.exponent.toNat + k)
    (hk_lo : FloatFormat.min_exp ≤ k) (hk_hi : k ≤ FloatFormat.max_exp) :
    ldexp k hk_lo hk_hi (ofBits b)
      = ofBits (FloatBits.setBiasedExponent E_new b) := by
  unfold ldexp
  exact (ofBits_setBiasedExponent_eq_fpMul_pow2
    (R := R) b k E_new hn_b hE_nz hE_not_allOnes hE_diff hk_lo hk_hi).symm

end Fp

/-! ## `fdim x y` = `max(x - y, 0)` -/

namespace Fp

variable [FloatFormat]

/-- **`fdim x y`** — positive difference. Composes `fpSub` with `fpRelu`
(Phase 3). Returns `0` when `x ≤ y`, else `x - y`. NaN-propagating via
`fpSub`. -/
noncomputable def fdim [RModeExec] (x y : Fp) : Fp :=
  fpRelu (fpSub x y)

/-- For finite operands with finite difference, `fdim` produces a finite
result of the form `Fp.finite (if c.s then 0 else c)` where `c = fpSub x y`
(the FiniteFp form). Math-level: `(if c.s then 0 else c).toVal = max 0 c.toVal`. -/
theorem fdim_finite_inner_toVal [RModeExec]
    (a b c : FiniteFp)
    (h_sub : fpSub (Fp.finite a) (Fp.finite b) = Fp.finite c) :
    fdim (Fp.finite a) (Fp.finite b)
      = Fp.finite (if c.s then (0 : FiniteFp) else c) := by
  unfold fdim
  rw [h_sub]
  exact fpRelu_finite_eq c

end Fp

/-! ## `ilogb` — integer-valued logB on normal inputs (bit-level corollary) -/

/-- **`FiniteFp.ilogb f : ℤ`** — the integer base-2 logarithm
`⌊log₂|f.toVal|⌋`. Aliases `FiniteFp.logBInt`. -/
@[reducible] def FiniteFp.ilogb [FloatFormat] (f : FiniteFp) : ℤ := f.logBInt

namespace Fp

/-- **Bit-level form of `ilogb`** for bit-normal inputs: the integer
base-2 logarithm equals the unbiased exponent (one subtraction in the
integer pipeline). Direct corollary of `FiniteFp.logBInt_normal`.

For a bit-normal `b`, decoding gives a value-level normal FiniteFp `f_b`,
whose `logBInt = f_b.e = b.toBitsTriple.exponent.toNat - exponentBias`. -/
theorem ilogb_of_normal_eq_unbiased_exponent
    [StdFloatFormat] (b : FloatBits)
    (hn : b.isNormal) :
    let f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand,
      FloatBits.isFinite_validFloatVal
        (FloatBits.notNaN_notInfinite b
          (fun ⟨h, _⟩ => hn.2 h) (fun ⟨h, _⟩ => hn.2 h))⟩
    f_b.logBInt
      = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := by
  simp only
  set f_b : FiniteFp := ⟨b.sign, b.FpExponent, b.FpSignificand, _⟩
  -- f_b is value-level normal (its decoded m is in the normal range).
  have hf_b_isNormal : _root_.isNormal f_b.m := by
    show _root_.isNormal b.FpSignificand
    refine ⟨?_, ?_⟩
    · -- 2^(prec-1) ≤ FpSignificand
      rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have hmsb : ((BitVec.ofBool true) ++ b.toBitsTriple.significand).msb = true := by
        simp [BitVec.msb, BitVec.getMsbD, BitVec.ofBool_true, BitVec.getLsbD_append]
      have hge := BitVec.toNat_ge_of_msb_true hmsb
      have h_eq : 1 + FloatFormat.significandBits - 1 = FloatFormat.significandBits := by
        have := FloatFormat.significandBits_pos; omega
      rw [h_eq] at hge
      exact hge
    · -- FpSignificand < 2^prec
      rw [FloatBits.FpSignificand_def, if_neg hn.1]
      have h_lt := ((BitVec.ofBool true) ++ b.toBitsTriple.significand).isLt
      exact h_lt.trans_eq (congr_arg (2 ^ ·) FloatFormat.one_plus_significandBits)
  -- f_b.m > 0 follows from isNormal (m ≥ 2^(prec-1) ≥ 2 since prec ≥ 2).
  have hf_b_m_pos : 0 < f_b.m := by
    have h1 : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f_b.m := hf_b_isNormal.1
    have h2 : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.pos_of_ne_zero (by positivity)
    omega
  -- f_b.e = bit-level FpExponent = E.toNat - bias (since b is bit-normal).
  have hf_b_e : f_b.e = (b.toBitsTriple.exponent.toNat : ℤ) - FloatFormat.exponentBias := by
    show b.FpExponent = _
    rw [FloatBits.FpExponent_def, if_neg hn.1]
  rw [FiniteFp.logBInt_normal f_b hf_b_m_pos hf_b_isNormal, hf_b_e]

end Fp
