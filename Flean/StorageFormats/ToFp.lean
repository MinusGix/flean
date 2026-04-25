import Flean.StorageFormats.Defs
import Flean.StorageFormats.Conversion
import Flean.Defs
import Flean.ToVal

/-!
# Widening: `StorageFp sf → FiniteFp ff_wide`

Exact (lossless) conversion from a storage float format (E4M3, BF16,
etc.) to a `FiniteFp` in a wider `FloatFormat` (e.g. Binary32,
Binary16).  Used in mixed-precision arithmetic, where narrow storage
values are widened for computation in a more accurate arithmetic
format, then narrowed back via `fromFp`.

The widening is value-preserving — no rounding, no error.

## The `FitsInNormal` precondition

`sf.FitsIn ff` says `ff` has at least as many significand bits and a
wider exponent range than `sf`.  That is *not* enough to guarantee
every sf-subnormal is ff-normal — if `ff.min_exp` is only slightly
below `1 - sf.bias`, small sf-subnormals may remain subnormal in ff.

`FitsInNormal` strengthens `FitsIn` with
`ff.min_exp ≤ 1 - sf.bias - sf.manBits`, which forces *every*
representable sf value (including the smallest sf-subnormal,
`2 ^ (1 - sf.bias - sf.manBits)`) into ff's normal range.  All
practical targets satisfy it (E4M3/E5M2/BF16 → Binary32 or Binary16,
except E5M2 → Binary16).  The general-subnormal case is left as
future work.
-/

namespace StorageFormat

/-- Strengthened `FitsIn`: every positive value representable in `sf`
lies in `ff`'s *normal* range (no sf→ff subnormals). -/
structure FitsInNormal (sf : StorageFormat) (ff : FloatFormat) : Prop
    extends sf.FitsIn ff where
  /-- ff's normal range starts at or below sf's smallest subnormal magnitude. -/
  min_exp_le_subnormal : ff.min_exp ≤ 1 - (sf.bias : ℤ) - (sf.manBits : ℤ)

end StorageFormat

/-! ### Concrete `FitsInNormal` instances

Practical pairs used in mixed-precision ML workloads.  Binary32 / BF16 are wide enough
to contain every sf-subnormal as a normal, so all sf → Binary32 and sf → BF16 widenings
are `FitsInNormal`.  Binary16 is only wide enough for E4M3 and E3M2 — the E5M2 /
E2M1 → Binary16 paths would need subnormal handling, deferred.
-/

theorem E4M3_fitsInNormal_Binary32 : E4M3.FitsInNormal FloatFormat.Binary32.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E5M2_fitsInNormal_Binary32 : E5M2.FitsInNormal FloatFormat.Binary32.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E3M2_fitsInNormal_Binary32 : E3M2.FitsInNormal FloatFormat.Binary32.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E2M3_fitsInNormal_Binary32 : E2M3.FitsInNormal FloatFormat.Binary32.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E2M1_fitsInNormal_Binary32 : E2M1.FitsInNormal FloatFormat.Binary32.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E4M3_fitsInNormal_Binary16 : E4M3.FitsInNormal FloatFormat.Binary16.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E3M2_fitsInNormal_Binary16 : E3M2.FitsInNormal FloatFormat.Binary16.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E4M3_fitsInNormal_BF16 : E4M3.FitsInNormal FloatFormat.BF16.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

theorem E5M2_fitsInNormal_BF16 : E5M2.FitsInNormal FloatFormat.BF16.toFloatFormat :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

namespace StorageFp

variable {f : StorageFormat}

/-! ### Effective-significand structure lemmas -/

/-- `v.effectiveSignificand < 2 ^ (f.manBits + 1)` (so it fits in `manBits + 1` bits). -/
theorem effectiveSignificand_lt (v : StorageFp f) :
    v.effectiveSignificand < 2 ^ (f.manBits + 1) := by
  have hman := v.man_lt
  unfold effectiveSignificand
  split
  · omega
  · calc 2 ^ f.manBits + v.man
        < 2 ^ f.manBits + 2 ^ f.manBits := by omega
      _ = 2 ^ (f.manBits + 1) := by ring

/-- For an sf-normal value (`¬ isExpZero`), `effectiveSignificand ≥ 2^manBits`. -/
theorem effectiveSignificand_ge_pow_manBits_of_not_isExpZero (v : StorageFp f)
    (h : ¬ v.isExpZero) : 2 ^ f.manBits ≤ v.effectiveSignificand := by
  unfold effectiveSignificand
  simp [h]

/-- For an sf-subnormal (`isExpZero`) value, `effectiveSignificand < 2^manBits`. -/
theorem effectiveSignificand_lt_pow_manBits_of_isExpZero (v : StorageFp f)
    (h : v.isExpZero) : v.effectiveSignificand < 2 ^ f.manBits := by
  unfold effectiveSignificand
  simp [h]
  exact v.man_lt

/-! ### Leading-bit position of the effective significand -/

/-- The leading-bit position of the effective significand (`Nat.log 2`). -/
def sigLog (v : StorageFp f) : ℕ := Nat.log 2 v.effectiveSignificand

theorem sigLog_le_manBits (v : StorageFp f) (hne : v.effectiveSignificand ≠ 0) :
    v.sigLog ≤ f.manBits := by
  unfold sigLog
  have := Nat.log_lt_of_lt_pow hne v.effectiveSignificand_lt
  omega

theorem pow_sigLog_le (v : StorageFp f) (hne : v.effectiveSignificand ≠ 0) :
    2 ^ v.sigLog ≤ v.effectiveSignificand :=
  Nat.pow_log_le_self 2 hne

theorem lt_pow_succ_sigLog (v : StorageFp f) :
    v.effectiveSignificand < 2 ^ (v.sigLog + 1) := by
  unfold sigLog
  by_cases hz : v.effectiveSignificand = 0
  · rw [hz]; exact Nat.one_le_two_pow
  · exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- In sf-normal values, `sigLog = manBits`. -/
theorem sigLog_eq_manBits_of_not_isExpZero (v : StorageFp f)
    (h : ¬ v.isExpZero) : v.sigLog = f.manBits := by
  unfold sigLog
  have h_lb : 2 ^ f.manBits ≤ v.effectiveSignificand :=
    v.effectiveSignificand_ge_pow_manBits_of_not_isExpZero h
  have h_ub : v.effectiveSignificand < 2 ^ (f.manBits + 1) := v.effectiveSignificand_lt
  have hne : v.effectiveSignificand ≠ 0 := by
    intro hz; rw [hz] at h_lb; simp at h_lb
  have h_lower : f.manBits ≤ Nat.log 2 v.effectiveSignificand :=
    Nat.le_log_of_pow_le (by norm_num) h_lb
  have h_upper : Nat.log 2 v.effectiveSignificand < f.manBits + 1 :=
    Nat.log_lt_of_lt_pow hne h_ub
  omega

/-- In sf-subnormal values (`isExpZero`), `sigLog < manBits`. -/
theorem sigLog_lt_manBits_of_isExpZero (v : StorageFp f)
    (hz : v.isExpZero) (hne : v.effectiveSignificand ≠ 0) :
    v.sigLog < f.manBits := by
  unfold sigLog
  exact Nat.log_lt_of_lt_pow hne (v.effectiveSignificand_lt_pow_manBits_of_isExpZero hz)

/-! ### `unbiasedExp` bounds -/

theorem unbiasedExp_ge (v : StorageFp f) : (1 : ℤ) - (f.bias : ℤ) ≤ v.unbiasedExp := by
  unfold unbiasedExp
  split
  · exact le_refl _
  · rename_i hne
    have : 0 < v.exp := by unfold isExpZero at hne; omega
    omega

theorem unbiasedExp_eq_of_isExpZero (v : StorageFp f) (h : v.isExpZero) :
    v.unbiasedExp = 1 - (f.bias : ℤ) := by
  unfold unbiasedExp; simp [h]

theorem unbiasedExp_le_of_not_isExpZero_of_isFinite
    (v : StorageFp f) (hne : ¬ v.isExpZero) (hfin : v.isFinite) :
    v.unbiasedExp ≤ (f.maxExpField : ℤ) - (f.bias : ℤ) := by
  unfold unbiasedExp
  simp [hne]
  exact_mod_cast (v.exp_le_maxExpField_of_isFinite hfin)

/-! ### The widened `FiniteFp` — core construction -/

/-- Widen a nonzero finite `StorageFp` to a `FiniteFp` in the wider
`ff_wide`.  The effective significand is renormalized so the leading
bit sits at position `ff_wide.prec.toNat - 1`; the exponent is adjusted
to preserve the real value.

Under `FitsInNormal`, the result is always `ff_wide`-normal. -/
def toFiniteFpWiden_core (ff_wide : FloatFormat) (h : f.FitsInNormal ff_wide)
    (v : StorageFp f) (hfin : v.isFinite) (hne : v.effectiveSignificand ≠ 0) :
    @FiniteFp ff_wide := by
  letI : FloatFormat := ff_wide
  have hFI : f.FitsIn ff_wide := h.toFitsIn
  -- Derived bounds on sigLog
  have h_lg_le : v.sigLog ≤ f.manBits := v.sigLog_le_manBits hne
  -- Prec bounds
  have h_prec_pos : 0 < ff_wide.prec := by have := ff_wide.valid_prec; omega
  have h_prec_toNat_ge : f.manBits + 1 ≤ ff_wide.prec.toNat := by
    have hnn : (0 : ℤ) ≤ ff_wide.prec := le_of_lt h_prec_pos
    have := Int.toNat_of_nonneg hnn
    have hge : (f.manBits : ℤ) + 1 ≤ ff_wide.prec := hFI.prec_ge
    omega
  have h_lg_le_prec_sub_one : v.sigLog ≤ ff_wide.prec.toNat - 1 := by omega
  -- Build m_wide and e_wide
  let shift : ℕ := ff_wide.prec.toNat - 1 - v.sigLog
  let m_wide : ℕ := v.effectiveSignificand * 2 ^ shift
  let e_wide : ℤ := v.unbiasedExp + (v.sigLog : ℤ) - (f.manBits : ℤ)
  refine ⟨v.sign, e_wide, m_wide, ?_⟩
  -- Prep: shift algebra
  have h_shift_sum : v.sigLog + shift = ff_wide.prec.toNat - 1 := by
    simp [shift]; omega
  have h_shift_sum_succ : v.sigLog + 1 + shift = ff_wide.prec.toNat := by
    simp [shift]; omega
  -- m_wide lower: 2^(prec-1) ≤ m_wide
  have h_m_lb : 2 ^ (ff_wide.prec.toNat - 1) ≤ m_wide := by
    calc 2 ^ (ff_wide.prec.toNat - 1)
        = 2 ^ (v.sigLog + shift) := by rw [h_shift_sum]
      _ = 2 ^ v.sigLog * 2 ^ shift := by ring
      _ ≤ v.effectiveSignificand * 2 ^ shift :=
          Nat.mul_le_mul_right _ (v.pow_sigLog_le hne)
  -- m_wide upper: m_wide < 2^prec
  have h_m_ub : m_wide < 2 ^ ff_wide.prec.toNat := by
    have hlt : v.effectiveSignificand < 2 ^ (v.sigLog + 1) := v.lt_pow_succ_sigLog
    calc m_wide
        = v.effectiveSignificand * 2 ^ shift := rfl
      _ < 2 ^ (v.sigLog + 1) * 2 ^ shift :=
          Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 2 ^ (v.sigLog + 1 + shift) := by ring
      _ = 2 ^ ff_wide.prec.toNat := by rw [h_shift_sum_succ]
  -- isNormal: 2^((prec-1).toNat) ≤ m_wide < 2^(prec.toNat)
  have h_isNormal : _root_.isNormal m_wide := by
    refine ⟨?_, h_m_ub⟩
    rw [show (ff_wide.prec - 1).toNat = ff_wide.prec.toNat - 1 from
      FloatFormat.prec_sub_one_toNat_eq_toNat_sub]
    exact h_m_lb
  -- e_wide lower: ff_wide.min_exp ≤ e_wide
  have h_e_lb : ff_wide.min_exp ≤ e_wide := by
    -- From unbiasedExp ≥ 1 - bias and sigLog ≥ 0 and FitsInNormal.min_exp_le_subnormal:
    --   e_wide ≥ (1 - bias) + 0 - manBits = 1 - bias - manBits ≥ ff_wide.min_exp.
    have h1 := v.unbiasedExp_ge
    have h_sub := h.min_exp_le_subnormal
    have h_lg_nn : (0 : ℤ) ≤ (v.sigLog : ℤ) := Int.natCast_nonneg _
    simp only [e_wide]
    linarith
  -- e_wide upper: e_wide ≤ ff_wide.max_exp
  have h_e_ub : e_wide ≤ ff_wide.max_exp := by
    by_cases hz : v.isExpZero
    · -- sf-subnormal: sigLog < manBits, e_wide ≤ -bias ≤ 0 ≤ 1 ≤ ff_wide.max_exp.
      have h_lg_lt : v.sigLog < f.manBits := v.sigLog_lt_manBits_of_isExpZero hz hne
      have h_ue := v.unbiasedExp_eq_of_isExpZero hz
      have h_max_pos : (1 : ℤ) ≤ ff_wide.max_exp := ff_wide.max_exp_pos
      simp only [e_wide, h_ue]
      have hbias_nn : (0 : ℤ) ≤ (f.bias : ℤ) := Int.natCast_nonneg _
      linarith
    · -- sf-normal: sigLog = manBits, so e_wide = unbiasedExp ≤ maxExpField - bias ≤ max_exp.
      have h_lg_eq : v.sigLog = f.manBits := v.sigLog_eq_manBits_of_not_isExpZero hz
      have h_ue := v.unbiasedExp_le_of_not_isExpZero_of_isFinite hz hfin
      have h_fi_max := hFI.max_exp_ge
      simp only [e_wide, h_lg_eq]
      have : v.unbiasedExp + (f.manBits : ℤ) - (f.manBits : ℤ) = v.unbiasedExp := by ring
      rw [this]
      linarith
  -- Assemble validity
  refine ⟨h_e_lb, h_e_ub, h_m_ub, Or.inl h_isNormal⟩

/-! ### The widened `FiniteFp` — total version -/

/-- Widen a finite `StorageFp` to a `FiniteFp` in the wider `ff_wide`.
Zero values map to `FiniteFp.zero`; nonzero values renormalize via
`toFiniteFpWiden_core`. -/
def toFiniteFpWiden (ff_wide : FloatFormat) (h : f.FitsInNormal ff_wide)
    (v : StorageFp f) (hfin : v.isFinite) : @FiniteFp ff_wide :=
  letI : FloatFormat := ff_wide
  if hne : v.effectiveSignificand = 0 then
    (0 : FiniteFp)
  else
    toFiniteFpWiden_core ff_wide h v hfin hne

/-! ### Value preservation -/

/-- Widening preserves the real value. -/
theorem toFiniteFpWiden_toVal {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (ff_wide : FloatFormat) (h : f.FitsInNormal ff_wide)
    (v : StorageFp f) (hfin : v.isFinite) :
    @FiniteFp.toVal ff_wide R _ (v.toFiniteFpWiden ff_wide h hfin) = v.toVal := by
  letI : FloatFormat := ff_wide
  unfold toFiniteFpWiden
  split
  · -- zero branch
    rename_i hz
    rw [FiniteFp.toVal_zero]
    unfold toVal signVal
    have hzR : (v.effectiveSignificand : R) = 0 := by rw [hz]; simp
    rw [hzR]; ring
  · -- nonzero branch
    rename_i hne
    unfold toFiniteFpWiden_core
    -- Unfold both FiniteFp.toVal and StorageFp.toVal; identify signs; reduce to
    -- the magnitude identity `eff * 2^shift * 2^(e_wide - prec + 1) = eff * 2^(unbiasedExp - manBits)`.
    simp only [FiniteFp.toVal, FiniteFp.sign', FloatFormat.radix_val_eq_two]
    unfold toVal signVal
    -- Prec-cast lemma.
    have h_prec_toNat_eq : (ff_wide.prec.toNat : ℤ) = ff_wide.prec := by
      have hnn : (0 : ℤ) ≤ ff_wide.prec := by have := ff_wide.valid_prec; omega
      exact_mod_cast Int.toNat_of_nonneg hnn
    have hFI : f.FitsIn ff_wide := h.toFitsIn
    have h_prec_toNat_ge : f.manBits + 1 ≤ ff_wide.prec.toNat := by
      have hge : (f.manBits : ℤ) + 1 ≤ ff_wide.prec := hFI.prec_ge
      have hnn : (0 : ℤ) ≤ ff_wide.prec := by have := ff_wide.valid_prec; omega
      have := Int.toNat_of_nonneg hnn; omega
    have h_lg_le : v.sigLog ≤ f.manBits := v.sigLog_le_manBits hne
    have h_lg_le_prec : v.sigLog ≤ ff_wide.prec.toNat - 1 := by omega
    -- Core arithmetic identity: shift + (e_wide - prec + 1) = unbiasedExp - manBits.
    have h_exp_eq :
        ((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ)
          + (v.unbiasedExp + (v.sigLog : ℤ) - (f.manBits : ℤ)) - ff_wide.prec + 1
          = v.unbiasedExp - (f.manBits : ℤ) := by
      -- prec.toNat - 1 - sigLog nonneg because sigLog ≤ prec.toNat - 1
      rw [show ((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ)
            = (ff_wide.prec.toNat : ℤ) - 1 - v.sigLog from by omega]
      rw [h_prec_toNat_eq]; ring
    -- Reduce the LHS via zpow_add to expose the identity.
    have h_two_ne : (2 : R) ≠ 0 := by norm_num
    have h_pow :
        (2 : R) ^ (((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ)) *
        (2 : R) ^ (v.unbiasedExp + (v.sigLog : ℤ) - (f.manBits : ℤ) - ff_wide.prec + 1)
          = (2 : R) ^ (v.unbiasedExp - (f.manBits : ℤ)) := by
      rw [← zpow_add₀ h_two_ne]
      congr 1
      linarith [h_exp_eq]
    -- Reshape LHS
    have h_m : ((v.effectiveSignificand * 2 ^ (ff_wide.prec.toNat - 1 - v.sigLog) : ℕ) : R)
        = (v.effectiveSignificand : R) * (2 : R) ^ ((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ) := by
      push_cast; rw [zpow_natCast]
    rw [h_m]
    push_cast
    -- Group the two zpow factors and apply h_pow
    rw [show
      ((if v.sign = true then -1 else 1) : R)
        * ((v.effectiveSignificand : R) * (2 : R) ^ ((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ))
        * (2 : R) ^ (v.unbiasedExp + (v.sigLog : ℤ) - (f.manBits : ℤ) - ff_wide.prec + 1)
        = ((if v.sign = true then -1 else 1) : R)
          * (v.effectiveSignificand : R)
          * ((2 : R) ^ ((ff_wide.prec.toNat - 1 - v.sigLog : ℕ) : ℤ)
              * (2 : R) ^ (v.unbiasedExp + (v.sigLog : ℤ) - (f.manBits : ℤ) - ff_wide.prec + 1))
      from by ring]
    rw [h_pow]

end StorageFp
