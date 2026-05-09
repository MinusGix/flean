import Flean.IntegerEquivalence.LibmIntrinsics

/-! # FP ↔ Integer equivalence: `frexp`

Phase 1.8 expansion. `frexp x` splits `x = m · 2^e` with `m ∈ [0.5, 1)`.

For finite normal inputs, the bit-level form is "set the biased exponent to
`bias - 1` (which decodes to unbiased exponent `-1`, giving `m ∈ [0.5, 1)`)
and output the original unbiased exponent + 1". A single `setBiasedExponent`
op + a single integer subtract.

Subnormal and infinity/NaN edge cases are deferred — the headline value
is the normal-input case, which dominates real usage.

This file ships the value-level structural definitions and the reconstruction
identity. The literal "set biased exponent at the bit level" form is
already covered by `setBiasedExponent` from `MulPow2.lean`; users can compose
the structural identity here with that workhorse to get the bit-level form.

Hypothesis on the format: `min_exp ≤ -1`. All real binary FP formats
(Binary16/32/64/128, BFloat16, all TF32/E4M3/E5M2/E3M2 variants) satisfy
this; only pathologically small formats with `max_exp = 1` would not. -/

namespace FiniteFp

variable [FloatFormat]

/-- For normal `f`, the FiniteFp obtained by setting the unbiased exponent
to `-1` is well-defined when `min_exp ≤ -1`. -/
private theorem frexp_valid_of_normal
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    IsValidFiniteVal (-1) f.m := by
  refine ⟨h_min_exp, ?_, ?_, Or.inl hn⟩
  · have := FloatFormat.max_exp_pos; omega
  · exact f.valid.2.2.1

/-- **`frexp_significand f`** for normal `f`: the FiniteFp with same sign
and significand but unbiased exponent `-1`, giving `toVal ∈ [-1, -0.5] ∪ [0.5, 1)`. -/
def frexp_significand
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) : FiniteFp :=
  ⟨f.s, -1, f.m, frexp_valid_of_normal f hn h_min_exp⟩

/-- **`frexp_exponent f`** = `f.e + 1` — the unbiased exponent + 1. -/
def frexp_exponent (f : FiniteFp) : ℤ := f.e + 1

@[simp] theorem frexp_significand_s
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    (frexp_significand f hn h_min_exp).s = f.s := rfl

@[simp] theorem frexp_significand_e
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    (frexp_significand f hn h_min_exp).e = -1 := rfl

@[simp] theorem frexp_significand_m
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    (frexp_significand f hn h_min_exp).m = f.m := rfl

/-- **Reconstruction identity.** For normal `f`,
`f.toVal = (frexp_significand f hn).toVal · 2^(frexp_exponent f)`. -/
theorem frexp_reconstruct {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    (f.toVal : R) =
      ((frexp_significand f hn h_min_exp).toVal : R) *
        (2 : R) ^ (frexp_exponent f) := by
  set g := frexp_significand f hn h_min_exp with hg_def
  unfold frexp_exponent
  -- Both f and g have the same sign. Express their toVal in the same form.
  by_cases hs : f.s
  · -- Negative case: route through `-f`/`-g`.
    have h_neg_f_pos : (-f).s = false := by rw [FiniteFp.neg_def]; simp [hs]
    have hgs : g.s = true := by show f.s = true; exact hs
    have h_neg_g_pos : (-g).s = false := by rw [FiniteFp.neg_def]; simp [hgs]
    have hg_e : g.e = -1 := rfl
    have hg_m : g.m = f.m := rfl
    rw [show f.toVal (R := R) = -((-f).toVal) from by
          rw [FiniteFp.toVal_neg_eq_neg]; ring,
        show g.toVal (R := R) = -((-g).toVal) from by
          rw [FiniteFp.toVal_neg_eq_neg]; ring,
        FiniteFp.toVal_pos_eq (-f) h_neg_f_pos,
        FiniteFp.toVal_pos_eq (-g) h_neg_g_pos]
    -- (-g).e = g.e = -1, (-g).m = f.m. (-f).e = f.e, (-f).m = f.m.
    have h_neg_g_e : (-g).e = -1 := by rw [FiniteFp.neg_def]; exact hg_e
    have h_neg_g_m : (-g).m = f.m := by rw [FiniteFp.neg_def]; exact hg_m
    have h_neg_f_e : (-f).e = f.e := by rw [FiniteFp.neg_def]
    have h_neg_f_m : (-f).m = f.m := by rw [FiniteFp.neg_def]
    rw [h_neg_g_e, h_neg_g_m, h_neg_f_e, h_neg_f_m]
    -- Goal: -(f.m * 2^(f.e - prec + 1))
    --     = -(f.m * 2^(-1 - prec + 1)) * 2^(f.e + 1)
    have h_split : (f.e - FloatFormat.prec + 1 : ℤ)
          = (-1 - FloatFormat.prec + 1) + (f.e + 1) := by ring
    rw [h_split, zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
    ring
  · -- Positive case
    rw [Bool.not_eq_true] at hs
    have hgs : g.s = false := by show f.s = false; exact hs
    rw [FiniteFp.toVal_pos_eq f hs, FiniteFp.toVal_pos_eq g hgs]
    have hg_e : g.e = -1 := rfl
    have hg_m : g.m = f.m := rfl
    rw [hg_e, hg_m]
    have h_split : (f.e - FloatFormat.prec + 1 : ℤ)
          = (-1 - FloatFormat.prec + 1) + (f.e + 1) := by ring
    rw [h_split, zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
    ring

/-- **Range bound.** For normal `f`, the magnitude of `frexp_significand f`
lies in `[0.5, 1)`. -/
theorem frexp_significand_abs_in_half_one {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (f : FiniteFp)
    (hn : _root_.isNormal f.m)
    (h_min_exp : FloatFormat.min_exp ≤ -1) :
    (1 / 2 : R) ≤ |((frexp_significand f hn h_min_exp).toVal : R)|
      ∧ |((frexp_significand f hn h_min_exp).toVal : R)| < 1 := by
  set g := frexp_significand f hn h_min_exp with hg_def
  have hg_e : g.e = -1 := rfl
  have hg_m : g.m = f.m := rfl
  have hm_lower : (2 : ℕ) ^ (FloatFormat.prec - 1).toNat ≤ f.m := hn.1
  have hm_upper := f.valid.2.2.1
  have h_abs : |(g.toVal : R)|
        = (f.m : R) * (2 : R) ^ (-FloatFormat.prec : ℤ) := by
    rw [← FiniteFp.toVal_mag_toVal_abs (R := R)]
    show (FiniteFp.toVal_mag _ : R) = _
    unfold FiniteFp.toVal_mag
    rw [hg_e, hg_m, FloatFormat.radix_val_eq_two]
    push_cast
    show (f.m : R) * (2 : R) ^ (-1 - FloatFormat.prec + 1 : ℤ)
          = (f.m : R) * (2 : R) ^ (-FloatFormat.prec : ℤ)
    congr 1; congr 1; ring
  rw [h_abs]
  have h_pow_pos : (0 : R) < (2 : R) ^ (-FloatFormat.prec : ℤ) := by positivity
  refine ⟨?_, ?_⟩
  · -- f.m * 2^(-prec) ≥ 2^(prec-1) * 2^(-prec) = 1/2.
    have h_lower : (2 : R) ^ ((FloatFormat.prec - 1).toNat : ℤ) ≤ (f.m : R) := by
      rw [zpow_natCast]
      exact_mod_cast hm_lower
    calc (1 / 2 : R)
        = (2 : R) ^ ((FloatFormat.prec - 1).toNat : ℤ)
          * (2 : R) ^ (-FloatFormat.prec : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
          rw [show (((FloatFormat.prec - 1).toNat : ℤ) + (-FloatFormat.prec : ℤ) : ℤ)
                = -1 from by
              rw [FloatFormat.prec_sub_one_toNat_eq]; ring]
          norm_num
      _ ≤ (f.m : R) * (2 : R) ^ (-FloatFormat.prec : ℤ) :=
          mul_le_mul_of_nonneg_right h_lower (le_of_lt h_pow_pos)
  · -- f.m * 2^(-prec) < 2^prec * 2^(-prec) = 1.
    have h_upper : (f.m : R) < (2 : R) ^ (FloatFormat.prec.toNat : ℤ) := by
      rw [zpow_natCast]
      exact_mod_cast hm_upper
    calc (f.m : R) * (2 : R) ^ (-FloatFormat.prec : ℤ)
        < (2 : R) ^ (FloatFormat.prec.toNat : ℤ)
          * (2 : R) ^ (-FloatFormat.prec : ℤ) :=
          mul_lt_mul_of_pos_right h_upper h_pow_pos
      _ = 1 := by
          rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]
          rw [show ((FloatFormat.prec.toNat : ℤ) + (-FloatFormat.prec : ℤ) : ℤ)
                = 0 from by rw [FloatFormat.prec_toNat_eq]; ring]
          norm_num

end FiniteFp
