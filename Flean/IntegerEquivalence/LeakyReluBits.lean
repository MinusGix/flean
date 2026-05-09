import Flean.IntegerEquivalence.ReluBits
import Flean.IntegerEquivalence.MulPow2

/-! # FP ↔ Integer equivalence: leaky ReLU with `2^(-k)` slope

Phase 3 expansion of the FP ↔ Integer equivalence area.

For a leak slope `α = 2^(-k)` (k ≥ 1), the leaky-ReLU `x ↦ if x ≥ 0 then x else
α·x` decomposes into a sign-bit-dispatched select:

* Non-negative inputs pass through unchanged (same as ReLU).
* Negative inputs have their biased exponent decreased by `k` — pure
  `setBiasedExponent` op at the bit level, no FP multiplication needed.

This composes today's `bitRelu` with `setBiasedExponent` (= `fpMul_pow2`
at the value level).

* `Fp.fpLeakyRelu k _ _ x` — FP-level operator parametric in slope exponent.
* `FloatBits.bitLeakyRelu E b` — bit-level operator (caller supplies the
  new biased exponent `E` for the negative branch).
* `ofBits_bitLeakyRelu_eq_fpLeakyRelu` — bridge for finite normal inputs
  with normal-range result (same carve-out as `fpMul_pow2`).

The carve-out is the same as `ofBits_setBiasedExponent_eq_fpMul_pow2`:
input bit-normal, new biased exponent in normal range. Subnormal and
overflow extensions are natural follow-ups. -/

namespace Fp

variable [FloatFormat]

/-- **FP-level leaky ReLU** with slope `pow2Float (-k)`. For `x ≥ 0`,
returns `x`; for `x < 0`, returns `x · 2^(-k)` (= `x / 2^k`). -/
noncomputable def fpLeakyRelu [FloatFormat] [RModeExec]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ -k)
    (hk_hi : -k ≤ FloatFormat.max_exp)
    (x : Fp) : Fp :=
  if x.sign then fpMul x (Fp.finite (pow2Float (-k) hk_lo hk_hi))
  else x

end Fp

namespace Fp.FloatBits

variable [FloatFormat]

/-- **Bit-level leaky ReLU.** For non-negative inputs (sign = false),
returns the input unchanged. For negative inputs (sign = true), replaces
the biased exponent with `E_new` (the caller supplies this — typically
`b.toBitsTriple.exponent - k_bv` for slope `2^(-k)`). -/
def bitLeakyRelu (E_new : BitVec FloatFormat.exponentBits) (b : FloatBits) :
    FloatBits :=
  if b.sign then setBiasedExponent E_new b else b

@[simp] theorem bitLeakyRelu_pos (E_new : BitVec FloatFormat.exponentBits)
    (b : FloatBits) (hs : b.sign = false) :
    bitLeakyRelu E_new b = b := by
  unfold bitLeakyRelu; rw [hs]; simp

@[simp] theorem bitLeakyRelu_neg (E_new : BitVec FloatFormat.exponentBits)
    (b : FloatBits) (hs : b.sign = true) :
    bitLeakyRelu E_new b = setBiasedExponent E_new b := by
  unfold bitLeakyRelu; rw [hs]; simp

end Fp.FloatBits

/-! ## Bit-level bridge -/

namespace Fp

/-- **Bit-level leaky ReLU bridge.** For a bit-normal `b` with `E_new` also
in the normal range, decoding `bitLeakyRelu E_new b` agrees with
`fpLeakyRelu k _ _ (ofBits b)` — composition of `bitRelu`'s sign-dispatch
with `setBiasedExponent`'s decrement-equals-`fpMul-by-pow2` bridge.

The non-negative branch is just `b` (decoded). The negative branch decodes
to `fpMul (ofBits b) (pow2Float (-k))` via the existing
`ofBits_setBiasedExponent_eq_fpMul_pow2`. -/
theorem ofBits_bitLeakyRelu_eq_fpLeakyRelu
    [StdFloatFormat] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (b : FloatBits) (k : ℤ) (E_new : BitVec FloatFormat.exponentBits)
    (hn_b : b.isNormal)
    (hE_nz : E_new ≠ 0)
    (hE_not_allOnes : E_new ≠ BitVec.allOnes FloatFormat.exponentBits)
    (hE_diff : (E_new.toNat : ℤ) = b.toBitsTriple.exponent.toNat + (-k))
    (hk_lo : FloatFormat.min_exp ≤ -k) (hk_hi : -k ≤ FloatFormat.max_exp) :
    ofBits (FloatBits.bitLeakyRelu E_new b)
      = fpLeakyRelu k hk_lo hk_hi (ofBits b) := by
  -- b is finite (normal ⇒ finite).
  have hf_b : b.isFinite := FloatBits.notNaN_notInfinite b
    (fun ⟨h, _⟩ => hn_b.2 h) (fun ⟨h, _⟩ => hn_b.2 h)
  have hn_b_b : ¬b.isNaN := hf_b.1
  -- ofBits b is finite, so ofBits.sign = b.sign.
  have hs_eq : (ofBits b).sign = b.sign := ofBits_sign b hn_b_b
  unfold FloatBits.bitLeakyRelu fpLeakyRelu
  rw [hs_eq]
  by_cases hs : b.sign
  · -- Negative branch: setBiasedExponent ↔ fpMul pow2Float
    rw [if_pos hs, if_pos hs]
    exact ofBits_setBiasedExponent_eq_fpMul_pow2
      (R := R) b (-k) E_new hn_b hE_nz hE_not_allOnes hE_diff hk_lo hk_hi
  · -- Non-negative branch: passthrough.
    rw [if_neg hs, if_neg hs]

end Fp

/-! ## Math-level connection: leaky-ReLU value formula -/

namespace Fp

variable [FloatFormat]

/-- For a positive `f` (s = false), `fpLeakyRelu` returns `f` (passthrough). -/
@[simp] theorem fpLeakyRelu_pos {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (k : ℤ) (hk_lo : FloatFormat.min_exp ≤ -k)
    (hk_hi : -k ≤ FloatFormat.max_exp)
    (x : Fp) (hs : x.sign = false) :
    fpLeakyRelu k hk_lo hk_hi x = x := by
  unfold fpLeakyRelu; simp [hs]

/-- For a negative `Fp.finite f` (s = true) that's bit-normal with the result
also in normal range, `fpLeakyRelu` produces the structural FiniteFp with
exponent decreased by `k`. -/
theorem fpLeakyRelu_finite_neg_normal_eq
    [StdFloatFormat] {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RModeExec]
    [RoundIntSigMSound R] [RModeIdem R]
    (f : FiniteFp) (k : ℤ)
    (hf_normal : _root_.isNormal f.m)
    (hk_lo : FloatFormat.min_exp ≤ -k)
    (hk_hi : -k ≤ FloatFormat.max_exp)
    (hs : f.s = true)
    (hres_lo : FloatFormat.min_exp ≤ f.e + (-k))
    (hres_hi : f.e + (-k) ≤ FloatFormat.max_exp) :
    fpLeakyRelu k hk_lo hk_hi (Fp.finite f) =
      Fp.finite ⟨f.s, f.e + (-k), f.m,
        isValidFiniteVal_shift_normal hf_normal hres_lo hres_hi⟩ := by
  unfold fpLeakyRelu
  have hsf : (Fp.finite f).sign = true := hs
  rw [if_pos hsf]
  -- Use fpMul_pow2_normal_eq.
  have h := fpMul_pow2_normal_eq (R := R) f (-k) hf_normal hk_lo hk_hi hres_lo hres_hi
  show fpMul (Fp.finite f) (Fp.finite (pow2Float (-k) hk_lo hk_hi)) = _
  rw [show fpMul (Fp.finite f) (Fp.finite (pow2Float (-k) hk_lo hk_hi))
        = f * pow2Float (-k) hk_lo hk_hi from by
    simp [mul_eq_fpMul, fpMul_coe_coe, ← mul_finite_eq_fpMulFinite]]
  exact h

/-- For a negative finite `f`, the structural FiniteFp result of
`fpLeakyRelu` on the negative branch has `toVal = 2^(-k) · f.toVal` over
any ordered field — the standard math-level leaky-ReLU formula. -/
theorem fpLeakyRelu_finite_neg_toVal
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : FiniteFp) (k : ℤ)
    (hf_normal : _root_.isNormal f.m)
    (hs : f.s = true)
    (hres_lo : FloatFormat.min_exp ≤ f.e + (-k))
    (hres_hi : f.e + (-k) ≤ FloatFormat.max_exp) :
    let g : FiniteFp := ⟨f.s, f.e + (-k), f.m,
      isValidFiniteVal_shift_normal hf_normal hres_lo hres_hi⟩
    (g.toVal : R) = (2 : R) ^ (-k) * (f.toVal : R) := by
  simp only
  set g : FiniteFp := ⟨f.s, f.e + (-k), f.m,
    isValidFiniteVal_shift_normal hf_normal hres_lo hres_hi⟩ with hg_def
  -- For both f and g (s = true), toVal = -((-f).toVal) and the magnitude
  -- formula gives a clean factor of 2^(-k).
  have hgs : g.s = true := hs
  have h_neg_g_pos : (-g).s = false := by rw [FiniteFp.neg_def]; simp [hgs]
  have h_neg_f_pos : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
  rw [show g.toVal (R := R) = -((-g).toVal) from by
        rw [FiniteFp.toVal_neg_eq_neg]; ring,
      show f.toVal (R := R) = -((-f).toVal) from by
        rw [FiniteFp.toVal_neg_eq_neg]; ring,
      FiniteFp.toVal_pos_eq (-g) h_neg_g_pos,
      FiniteFp.toVal_pos_eq (-f) h_neg_f_pos]
  -- (-g).e = f.e + (-k), (-g).m = f.m, (-f).e = f.e, (-f).m = f.m.
  show -((f.m : R) * (2 : R) ^ (f.e + (-k) - FloatFormat.prec + 1))
        = (2 : R) ^ (-k) * -((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1))
  rw [show (f.e + (-k) - FloatFormat.prec + 1 : ℤ)
        = (f.e - FloatFormat.prec + 1) + (-k) from by ring,
      zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
  ring

end Fp
