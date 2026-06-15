import Flean.Operations.ExactInt

/-! # Fixed-point exact arithmetic (scaled integers)

`ExactInt` reduces float ops on *integer-valued* floats to integer arithmetic. This file
widens the range to **fixed-point** values: a float that equals `m · 2^s` for an integer
`m` and a common scale `s`. (`ExactInt` is the `s = 0` case.)

The reduction is the same in spirit — exactness of `fpAdd`/`fpMul` doesn't care about the
scale, only about whether the result is representable — but the scale is the natural
coordinate for *block-structured* and *fixed-point* reasoning, and it is the substrate the
correction layer sits on: arithmetic stays exact while the integer `m` fits in `prec` bits
at scale `s`, and the **correction** appears only on renormalization (a result needing more
than `prec` bits), which is the next piece.

`ScaledExact R` carries the float as honest data (as in `ExactIntAlgebra`): `fp`, the ideal
`(m, s)`, and `agree : fp.toVal = m · 2^s`.

NOTE: the correction layer (the inexact regime) is deliberately *not* here. It needs a
committed rounding policy (no generic `○`-level error bound exists — only mode-specific
ones like `roundNearestTiesToEven_abs_error_le_ulp_half`, which also need `isNormalRange`).
That is its own focused file. Subtraction/negation and the `.fp` provenance bridges mirror
`ExactIntAlgebra` and are TODO until a consumer needs them.
-/

section ScaledExact

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

omit [FloorRing R] [RModeExec] [RoundIntSigMSound R] in
/-- Helper: a nonzero integer `r` at an in-range scale `e_base` has its rounded value
exact (`○(r · 2^e_base)` returns the float representing it). The scaled analogue of
`int_round_exact`. -/
private theorem scaled_round_exact (r e_base : ℤ) (hr : r ≠ 0)
    (hr_bound : r.natAbs < 2 ^ FloatFormat.prec.toNat)
    (he_lo : FloatFormat.min_exp - FloatFormat.prec + 1 ≤ e_base)
    (he_hi : e_base + FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, ○(((r : R) * 2 ^ e_base)) = f ∧ (f.toVal : R) = (r : R) * 2 ^ e_base := by
  obtain ⟨g, hg_nz, hg_val⟩ :=
    exists_finiteFp_of_int_mul_zpow (R := R) r e_base hr hr_bound he_lo he_hi
  have hgm : g.m ≠ 0 := by
    intro h0
    have hz : (g.toVal : R) = 0 := (FiniteFp.toVal_significand_zero_iff (R := R)).mp h0
    rw [hg_val] at hz
    exact (mul_ne_zero (by exact_mod_cast hr) (by positivity)) hz
  refine ⟨g, ?_, hg_val⟩
  rw [← hg_val]
  exact RModeIdem.round_idempotent (R := R) g (Or.inr (Nat.pos_of_ne_zero hgm))

/-- **Fixed-point exact addition.** Two floats at a common scale `s` add exactly when their
integer significands sum to a nonzero integer in `(-2^prec, 2^prec)`. -/
theorem fpAddFinite_scaled_exact (a b : FiniteFp) (m_a m_b s : ℤ)
    (ha : (a.toVal : R) = (m_a : R) * 2 ^ s) (hb : (b.toVal : R) = (m_b : R) * 2 ^ s)
    (hsum_nz : m_a + m_b ≠ 0)
    (hsum_bound : (m_a + m_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hs_lo : FloatFormat.min_exp - FloatFormat.prec + 1 ≤ s)
    (hs_hi : s + FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, a + b = f ∧ (f.toVal : R) = ((m_a + m_b : ℤ) : R) * 2 ^ s := by
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by
    rw [ha, hb, ← add_mul]
    exact mul_ne_zero (by rw [← Int.cast_add]; exact_mod_cast hsum_nz) (by positivity)
  obtain ⟨f, hf_round, hf_val⟩ :=
    scaled_round_exact (R := R) (m_a + m_b) s hsum_nz hsum_bound hs_lo hs_hi
  refine ⟨f, ?_, hf_val⟩
  calc
    a + b = ○((a.toVal : R) + b.toVal) := by
      simpa [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd] using
        fpAddFinite_correct (R := R) a b hsum_ne
    _ = ○(((m_a + m_b : ℤ) : R) * 2 ^ s) := by
      congr 1; rw [ha, hb, ← add_mul]; push_cast; ring
    _ = f := hf_round

/-- **Fixed-point exact multiplication.** Scales add (`s_a + s_b`); the result is exact when
the integer significands' product is a nonzero integer in `(-2^prec, 2^prec)`. -/
theorem fpMulFinite_scaled_exact (a b : FiniteFp) (m_a m_b s_a s_b : ℤ)
    (ha : (a.toVal : R) = (m_a : R) * 2 ^ s_a) (hb : (b.toVal : R) = (m_b : R) * 2 ^ s_b)
    (hprod_nz : m_a * m_b ≠ 0)
    (hprod_bound : (m_a * m_b).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hs_lo : FloatFormat.min_exp - FloatFormat.prec + 1 ≤ s_a + s_b)
    (hs_hi : s_a + s_b + FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, a * b = f ∧ (f.toVal : R) = ((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b) := by
  have hprod_ne : (a.toVal : R) * b.toVal ≠ 0 := by
    rw [ha, hb]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (left_ne_zero_of_mul hprod_nz)) (by positivity))
      (mul_ne_zero (by exact_mod_cast (right_ne_zero_of_mul hprod_nz)) (by positivity))
  obtain ⟨f, hf_round, hf_val⟩ :=
    scaled_round_exact (R := R) (m_a * m_b) (s_a + s_b) hprod_nz hprod_bound hs_lo hs_hi
  refine ⟨f, ?_, hf_val⟩
  calc
    a * b = ○((a.toVal : R) * b.toVal) := by
      simpa [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul] using
        fpMulFinite_correct (R := R) a b hprod_ne
    _ = ○(((m_a * m_b : ℤ) : R) * 2 ^ (s_a + s_b)) := by
      congr 1; rw [ha, hb]; rw [zpow_add₀ (by norm_num : (2 : R) ≠ 0)]; push_cast; ring
    _ = f := hf_round

/-! ## The carrying structure

`ScaledExact R` bundles the float with the fixed-point value it represents, as data — the
scaled analogue of `ExactInt`. The exact ops above promote to `addExact`/`mulExact` once a
consumer needs the data-carrying form; for now the structure + `ofVal` fix the representation
and the lemmas do the reductions. -/

/-- A float together with the fixed-point value `m · 2^s` it represents exactly. -/
structure ScaledExact (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  /-- The literal float value. -/
  fp : FiniteFp
  /-- Integer significand of the represented fixed-point value. -/
  m : ℤ
  /-- Scale (ulp exponent) of the represented fixed-point value. -/
  s : ℤ
  /-- Agreement: the float's real value is `m · 2^s`. -/
  agree : (fp.toVal : R) = (m : R) * 2 ^ s

/-- The represented real value, `m · 2^s`. -/
def ScaledExact.value (a : ScaledExact R) : R := (a.m : R) * 2 ^ a.s

omit [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R] in
@[simp] theorem ScaledExact.value_eq_toVal (a : ScaledExact R) :
    a.value = (a.fp.toVal : R) := a.agree.symm

end ScaledExact
