import Flean.Operations.Add
import Flean.Operations.TwoSum
import Flean.Operations.KahanSum
import Flean.Operations.TwoProduct
import Flean.Operations.HornerFMA
import Flean.Operations.Div
import Flean.Operations.Sqrt

/-! # Double-Double Arithmetic — Foundations

A `DoubleDouble` represents a real number as an unevaluated sum of two
floating-point numbers, `hi + lo`, providing roughly twice the precision of
the underlying format. The classical use is to extend a hardware double to a
"double-double" with ~106 bits of precision, but the construction is generic
in `FloatFormat`.

This file ships the foundations only:
- the `DoubleDouble` type and its real value `toVal`
- `Zero`, `One`, `Neg` instances
- the embedding `ofFiniteFp : FiniteFp → DoubleDouble`
- basic value lemmas

Renormalization, `dd_add`, `dd_mul`, etc. are layered on top in subsequent
files / sections.

Reference: Bailey, Hida, Li — *QD: A C++/Fortran-90 Double-Double and
Quad-Double Package* (2007); Joldes, Muller, Popescu, Tucker — *Tight and
rigorous error bounds for basic building blocks of double-word arithmetic*
(2017).
-/

variable [FloatFormat]

/-- An unevaluated pair `hi + lo` of floating-point numbers, used to
    represent real values to roughly twice the precision of the underlying
    format.

    No structural invariant is imposed at the type level; the predicate
    `DoubleDouble.IsNormalized` (defined alongside renormalization) captures
    the standard non-overlapping condition `hi = round(hi + lo)`. -/
@[ext]
structure DoubleDouble [FloatFormat] where
  hi : FiniteFp
  lo : FiniteFp
deriving Repr, DecidableEq

namespace DoubleDouble

/-! ## Real value -/

/-- The real number represented by a `DoubleDouble`, as the unevaluated sum
    `hi.toVal + lo.toVal`. Generic in the codomain `R`. -/
def toVal {R : Type*} [Field R] (dd : DoubleDouble) : R :=
  dd.hi.toVal + dd.lo.toVal

@[simp] theorem toVal_mk {R : Type*} [Field R] (hi lo : FiniteFp) :
    toVal (R := R) ⟨hi, lo⟩ = hi.toVal + lo.toVal := rfl

/-! ## Zero, one, negation -/

instance : Zero DoubleDouble := ⟨⟨0, 0⟩⟩

theorem zero_def : (0 : DoubleDouble) = ⟨0, 0⟩ := rfl

@[simp] theorem zero_hi : (0 : DoubleDouble).hi = 0 := rfl
@[simp] theorem zero_lo : (0 : DoubleDouble).lo = 0 := rfl

instance : One DoubleDouble := ⟨⟨1, 0⟩⟩

theorem one_def : (1 : DoubleDouble) = ⟨1, 0⟩ := rfl

@[simp] theorem one_hi : (1 : DoubleDouble).hi = 1 := rfl
@[simp] theorem one_lo : (1 : DoubleDouble).lo = 0 := rfl

instance : Neg DoubleDouble := ⟨fun dd => ⟨-dd.hi, -dd.lo⟩⟩

theorem neg_def (dd : DoubleDouble) : -dd = ⟨-dd.hi, -dd.lo⟩ := rfl

@[simp] theorem neg_hi (dd : DoubleDouble) : (-dd).hi = -dd.hi := rfl
@[simp] theorem neg_lo (dd : DoubleDouble) : (-dd).lo = -dd.lo := rfl

instance : InvolutiveNeg DoubleDouble := ⟨by
  intro dd
  ext <;> simp [neg_def]⟩

instance : Inhabited DoubleDouble := ⟨0⟩

/-! ## Embedding from `FiniteFp` -/

/-- Embed a single FP value as a `DoubleDouble` with `lo = 0`. -/
def ofFiniteFp (f : FiniteFp) : DoubleDouble := ⟨f, 0⟩

@[simp] theorem ofFiniteFp_hi (f : FiniteFp) : (ofFiniteFp f).hi = f := rfl
@[simp] theorem ofFiniteFp_lo (f : FiniteFp) : (ofFiniteFp f).lo = 0 := rfl

@[simp] theorem ofFiniteFp_zero : ofFiniteFp 0 = (0 : DoubleDouble) := rfl

@[simp] theorem ofFiniteFp_one : ofFiniteFp 1 = (1 : DoubleDouble) := rfl

/-! Note: `ofFiniteFp (-f) = -ofFiniteFp f` does **not** hold structurally
because `(0 : FiniteFp)` and `-(0 : FiniteFp)` differ in their sign bit.
The value-level version is `toVal_ofFiniteFp` composed with `toVal_neg`. -/

/-! ## Value lemmas -/

variable {R : Type*} [Field R]

@[simp] theorem toVal_zero : toVal (R := R) (0 : DoubleDouble) = 0 := by
  simp [toVal, zero_def]

@[simp] theorem toVal_one [LinearOrder R] [IsStrictOrderedRing R] :
    toVal (R := R) (1 : DoubleDouble) = 1 := by
  simp [toVal, one_def]

@[simp] theorem toVal_neg (dd : DoubleDouble) :
    toVal (R := R) (-dd) = -toVal (R := R) dd := by
  simp [toVal, neg_def]
  ring

@[simp] theorem toVal_ofFiniteFp (f : FiniteFp) :
    toVal (R := R) (ofFiniteFp f) = f.toVal := by
  simp [toVal, ofFiniteFp]

/-! ## Normalization predicate

A `DoubleDouble` is *normalized* over `R` when rounding `hi + lo` reproduces
`hi`'s value: every finite result of the FP-rounded addition agrees in value
with `hi.toVal`. Equivalent to the classical Bailey/QD non-overlapping
condition `|lo| ≤ ½·ulp(hi)` for round-to-nearest modes, but stated
operationally so it works under any `RModeExec`.

The trivially-true case (rounding overflows to `∞` / NaN, no `f` exists) is
not what we want in practice — Phase 1C bounds will combine `IsNormalized`
with explicit no-overflow hypotheses. -/

end DoubleDouble

section IsNormalized

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

/-- Bailey-style normalization: rounding `hi + lo` agrees in value with `hi`. -/
def DoubleDouble.IsNormalized (dd : DoubleDouble) : Prop :=
  ∀ ⦃f : FiniteFp⦄, dd.hi + dd.lo = Fp.finite f → (f.toVal : R) = dd.hi.toVal

namespace DoubleDouble

theorem isNormalized_zero : IsNormalized (R := R) (0 : DoubleDouble) := by
  intro f hf
  -- 0 + 0 rounds to a zero float; its value is 0 = (0 : DoubleDouble).hi.toVal
  have hz : (0 : FiniteFp).m = 0 := rfl
  have := fpAddFinite_zero_left_val (R := R) (0 : FiniteFp) (0 : FiniteFp) hz f hf
  rw [this, zero_hi, FiniteFp.toVal_zero]

theorem isNormalized_one : IsNormalized (R := R) (1 : DoubleDouble) := by
  intro f hf
  have hz : (0 : FiniteFp).m = 0 := rfl
  have := fpAddFinite_zero_right_val (R := R) (1 : FiniteFp) (0 : FiniteFp) hz f hf
  rw [this, one_hi]

theorem isNormalized_ofFiniteFp (f : FiniteFp) :
    IsNormalized (R := R) (ofFiniteFp f) := by
  intro g hg
  have hz : (0 : FiniteFp).m = 0 := rfl
  exact fpAddFinite_zero_right_val (R := R) f (0 : FiniteFp) hz g hg

end DoubleDouble

/-! ### Magnitude consequences of `IsNormalized`

The operational form of `IsNormalized` (rounding `hi + lo` reproduces `hi`'s
value) implies the classical *magnitude* form: the lo part is at most a
machine-epsilon multiple of the sum.

This is the workhorse corollary that bridges from the operational predicate
into quantitative bounds — used in `dd_sqrt`'s and `dd_div`'s
auto-quantitative bound theorems to bound `|residual.lo|` without further
hypotheses on residual's structure. -/

omit [RModeIdem R] in
/-- **Magnitude bound on `dd.lo` from `IsNormalized`.**

If `dd` is normalized and rounding `dd.hi + dd.lo` produces a finite float,
then `|dd.lo.toVal| ≤ η · |dd.hi + dd.lo|`. This is `fpAdd_error_or_zero`
combined with the fact that the rounded sum equals `dd.hi.toVal` (operational
IsNormalized).

For the cancellation case (`dd.hi + dd.lo = 0`), `dd.hi.toVal = 0` so
`dd.lo.toVal = 0` and the bound is `0 ≤ 0`. -/
theorem DoubleDouble.IsNormalized.lo_le_eta_sum
    [RModeNearest R]
    (dd : DoubleDouble) (hnorm : dd.IsNormalized (R := R))
    (f : FiniteFp) (hf : dd.hi + dd.lo = (f : Fp))
    (hsum_normal : isNormalRange ((dd.hi.toVal : R) + dd.lo.toVal) ∨
                   (dd.hi.toVal : R) + dd.lo.toVal = 0) :
    |dd.lo.toVal (R := R)| ≤ η * |(dd.hi.toVal : R) + dd.lo.toVal| := by
  -- From IsNormalized: f.toVal = dd.hi.toVal
  have h_f_val : (f.toVal : R) = dd.hi.toVal := hnorm hf
  -- From fpAdd_error_or_zero: |f.toVal - (hi + lo)| ≤ η · |hi + lo|
  have h_round := KahanSum.fpAdd_error_or_zero (R := R) dd.hi dd.lo f hf hsum_normal
  -- Substitute f.toVal = dd.hi.toVal
  rw [h_f_val] at h_round
  -- Now h_round : |dd.hi.toVal - (dd.hi.toVal + dd.lo.toVal)| ≤ η · |...|
  -- Simplify LHS: dd.hi - (dd.hi + dd.lo) = -dd.lo
  have h_eq : (dd.hi.toVal : R) - (dd.hi.toVal + dd.lo.toVal) = -dd.lo.toVal := by ring
  rw [h_eq, abs_neg] at h_round
  exact h_round

omit [RModeIdem R] in
/-- **Solved-form magnitude bound: `|lo| ≤ (η/(1−η))·|hi|`.**

When `η < 1` (always true for sane formats), the recursive bound
`|lo| ≤ η·|hi+lo|` solves to a multiple of `|hi|` alone. This is the more
familiar form found in textbooks. -/
theorem DoubleDouble.IsNormalized.lo_le_eta_hi_div
    [RModeNearest R]
    (dd : DoubleDouble) (hnorm : dd.IsNormalized (R := R))
    (f : FiniteFp) (hf : dd.hi + dd.lo = (f : Fp))
    (hsum_normal : isNormalRange ((dd.hi.toVal : R) + dd.lo.toVal) ∨
                   (dd.hi.toVal : R) + dd.lo.toVal = 0)
    (h_eta_lt_one : (η : R) < 1) :
    |dd.lo.toVal (R := R)| ≤ (η / (1 - η)) * |(dd.hi.toVal : R)| := by
  have h_loose := hnorm.lo_le_eta_sum (R := R) dd f hf hsum_normal
  -- η · |hi + lo| ≤ η · (|hi| + |lo|) by triangle
  have h_tri : |(dd.hi.toVal : R) + dd.lo.toVal| ≤ |dd.hi.toVal| + |dd.lo.toVal| :=
    abs_add_le _ _
  have h_eta_nn : 0 ≤ (η : R) := FloatFormat.hEps_nonneg
  have h1 : |dd.lo.toVal (R := R)| ≤ η * (|dd.hi.toVal| + |dd.lo.toVal|) :=
    h_loose.trans (by gcongr)
  -- Solve: |lo| ≤ η·|hi| + η·|lo| ⟹ |lo|·(1-η) ≤ η·|hi|
  have h2 : |dd.lo.toVal (R := R)| * (1 - η) ≤ η * |dd.hi.toVal| := by
    nlinarith [h1, abs_nonneg (dd.hi.toVal : R), abs_nonneg (dd.lo.toVal : R)]
  have h_one_sub_eta_pos : 0 < (1 - η : R) := by linarith
  -- Divide both sides by (1 - η) and simplify
  have h3 : |dd.lo.toVal (R := R)| ≤ η * |dd.hi.toVal| / (1 - η) :=
    (le_div_iff₀ h_one_sub_eta_pos).mpr h2
  calc |dd.lo.toVal (R := R)|
      ≤ η * |dd.hi.toVal| / (1 - η) := h3
    _ = η / (1 - η) * |dd.hi.toVal| := by ring

end IsNormalized

/-! ## TwoSum lifts to a normalized DoubleDouble

The classical 2Sum (Knuth/Møller) error-free transformation is precisely what
turns a pair of FP additions into a normalized double-double. Given any two
nonzero finite floats `a, b` with FP-rounded sum `s`, there exists a `t` such
that `s + t = a + b` exactly (TwoSum); the pair `⟨s, t⟩` is then a normalized
`DoubleDouble` whose value matches `a + b`.

This is the canonical bridge from the EFT layer (TwoSum/TwoProduct) into
the double-double precision tier. -/

section TwoSumDD

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- Helper: when the value-level sum is zero, `fpAddFinite` produces a zero
    float (significand zero). Bridges `fpAddFinite_exact_cancel_sign` to the
    value-level hypothesis. -/
private theorem fpAddFinite_m_eq_zero_of_toVal_sum_zero
    (a b : FiniteFp) (h_sum : (a.toVal : R) + b.toVal = 0)
    {f : FiniteFp} (hf : fpAddFinite a b = Fp.finite f) :
    f.m = 0 := by
  have hexact := fpAddFinite_exact_sum R a b
  set e_min := min a.e b.e
  set isum := addAlignedSumInt a b
  have h2ne : (2 : R) ^ (e_min - FloatFormat.prec + 1) ≠ 0 :=
    zpow_ne_zero _ (by norm_num)
  have hisum_zero_R : (isum : R) = 0 := by
    have : (isum : R) * (2 : R) ^ (e_min - FloatFormat.prec + 1) = 0 := by
      rw [← hexact]; exact h_sum
    exact (mul_eq_zero.mp this).resolve_right h2ne
  have hisum_zero : isum = 0 := by exact_mod_cast hisum_zero_R
  have hcancel := fpAddFinite_exact_cancel_sign a b hisum_zero
  rw [hcancel] at hf
  rw [(Fp.finite.inj hf).symm]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Value-witness form of normalization.**

If `s + t` (as real numbers) equals some other rounded sum `a + b`, then
the pair `⟨s, t⟩` is a normalized `DoubleDouble` over `R`. The hypothesis
`hs : a + b = s` (an FP-rounded equality) and `ht : s.toVal + t.toVal = a.toVal + b.toVal`
together encode the TwoSum identity: `s` is the rounding of `a + b`, and `t`
captures the residual exactly.

This is the workhorse lemma for proving DD outputs normalized; both
`twoSum_isDoubleDouble` and `dd_add`'s final renormalize step are corollaries. -/
theorem isNormalized_of_value_witness (a b s_fp t_fp : FiniteFp)
    (hs : a + b = (s_fp : Fp))
    (ht : (s_fp.toVal : R) + t_fp.toVal = a.toVal + b.toVal) :
    DoubleDouble.IsNormalized (R := R) ⟨s_fp, t_fp⟩ := by
  intro f hf
  by_cases h_sum : (s_fp.toVal : R) + t_fp.toVal = 0
  · -- Cancellation case
    have h_ab : (a.toVal : R) + b.toVal = 0 := ht ▸ h_sum
    have hs_m : s_fp.m = 0 :=
      fpAddFinite_m_eq_zero_of_toVal_sum_zero (R := R) a b h_ab hs
    have hf_m : f.m = 0 :=
      fpAddFinite_m_eq_zero_of_toVal_sum_zero (R := R) s_fp t_fp h_sum hf
    rw [(FiniteFp.toVal_significand_zero_iff (R := R)).mp hf_m,
        (FiniteFp.toVal_significand_zero_iff (R := R)).mp hs_m]
  · -- Generic case: both rounds give the same Fp value
    have h_ab : (a.toVal : R) + b.toVal ≠ 0 := ht ▸ h_sum
    have hcorr_ab := fpAddFinite_correct (R := R) a b h_ab
    have hcorr_st := fpAddFinite_correct (R := R) s_fp t_fp h_sum
    rw [ht] at hcorr_st
    simp only [add_eq_fpAdd, fpAdd_coe_coe]
      at hs hf hcorr_ab hcorr_st
    have h_round_eq : (Fp.finite s_fp : Fp) = Fp.finite f := by
      rw [← hs, hcorr_ab, ← hcorr_st, hf]
    rw [Fp.finite.inj h_round_eq]

omit [RModeIdem R] in
/-- **TwoSum lifts to a normalized DoubleDouble.**

For any two nonzero finite floats `a, b` whose FP-rounded sum is `s_fp`,
there exists `t_fp : FiniteFp` such that `⟨s_fp, t_fp⟩` is a normalized
`DoubleDouble` whose value equals `a.toVal + b.toVal` exactly. -/
theorem twoSum_isDoubleDouble (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (s_fp : FiniteFp)
    (hs : a + b = s_fp) :
    ∃ t_fp : FiniteFp,
      let dd : DoubleDouble := ⟨s_fp, t_fp⟩
      dd.toVal (R := R) = a.toVal + b.toVal ∧
      dd.IsNormalized (R := R) := by
  obtain ⟨t_fp, ht⟩ := twoSum_exact (R := R) a b ha_nz hb_nz s_fp hs
  exact ⟨t_fp, ht, isNormalized_of_value_witness (R := R) a b s_fp t_fp hs ht⟩

end TwoSumDD

/-! ## `dd_add`: addition of two DoubleDoubles

Two-DD addition based on the standard "TwoSum-renormalize" pattern (Knuth /
Møller, with a final TwoSum instead of Fast2Sum so no magnitude precondition
is needed):

```
(s_hi, e_hi)        := TwoSum(a.hi, b.hi)         -- exact
e_lo_partial        := round(e_hi + a.lo)         -- 1 round
e_lo                := round(e_lo_partial + b.lo) -- 1 round
(hi_out, lo_out)    := TwoSum(s_hi, e_lo)         -- exact
return ⟨hi_out, lo_out⟩
```

The two TwoSums are exact (`s_hi + e_hi = a.hi + b.hi`, `hi_out + lo_out = s_hi + e_lo`),
so the only error comes from rounding the lo channel. Specifically:

```
result.toVal = s_hi + e_lo                                      [final TwoSum exact]
            = (a.hi + b.hi) − e_hi + e_lo                       [first TwoSum exact]
            = (a + b)  + (e_lo − (e_hi + a.lo + b.lo))          [add/subtract a.lo + b.lo]
```

so the deviation is precisely the rounding error of the lo-channel computation:

```
result.toVal − (a + b) = e_lo − round(e_hi + a.lo + b.lo)
```

bounded by `(2η + η²)·|e_hi + a.lo + b.lo|` for two rounded adds.

The witnesses for each rounding step are bundled into `DDAddStep`. -/

section DDAdd

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one execution of double-double addition.

Bundles the FiniteFp results of every rounding step plus the two TwoSum
exactness identities. Construct via `DDAddStep.ofWitnesses` from concrete
no-overflow + nonzero-significand hypotheses, or manually if the witnesses
arise from a different EFT path. -/
structure DDAddStep (a b : DoubleDouble) where
  /-- TwoSum on the hi parts: rounded sum. -/
  s_hi : FiniteFp
  hs_hi : a.hi + b.hi = (s_hi : Fp)
  /-- TwoSum on the hi parts: error. -/
  e_hi : FiniteFp
  he_hi_exact : (s_hi.toVal : R) + e_hi.toVal = a.hi.toVal + b.hi.toVal
  /-- First lo-channel round: `e_lo_partial = round(e_hi + a.lo)`. -/
  e_lo_partial : FiniteFp
  he_lo_partial : e_hi + a.lo = (e_lo_partial : Fp)
  /-- Second lo-channel round: `e_lo = round(e_lo_partial + b.lo)`. -/
  e_lo : FiniteFp
  he_lo : e_lo_partial + b.lo = (e_lo : Fp)
  /-- Final TwoSum: rounded sum. -/
  hi_out : FiniteFp
  hhi_out : s_hi + e_lo = (hi_out : Fp)
  /-- Final TwoSum: error (the new lo). -/
  lo_out : FiniteFp
  hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = s_hi.toVal + e_lo.toVal

namespace DDAddStep

variable {a b : DoubleDouble} (step : DDAddStep (R := R) a b)

/-- The `DoubleDouble` produced by the step. -/
def result : DoubleDouble := ⟨step.hi_out, step.lo_out⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_hi : step.result.hi = step.hi_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_lo : step.result.lo = step.lo_out := rfl

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_add`.**

The result deviates from the true sum `a + b` by exactly the difference
between the computed `e_lo` and the ideal lo-channel value
`e_hi + a.lo + b.lo`. -/
theorem result_value :
    step.result.toVal (R := R) - (a.toVal + b.toVal) =
      step.e_lo.toVal - (step.e_hi.toVal + a.lo.toVal + b.lo.toVal) := by
  -- result.toVal = hi_out + lo_out = s_hi + e_lo (final TwoSum)
  have h_final : (step.hi_out.toVal : R) + step.lo_out.toVal =
      step.s_hi.toVal + step.e_lo.toVal := step.hlo_out_exact
  -- s_hi + e_hi = a.hi + b.hi (first TwoSum)
  have h_hi : (step.s_hi.toVal : R) + step.e_hi.toVal =
      a.hi.toVal + b.hi.toVal := step.he_hi_exact
  show step.result.toVal (R := R) - (a.toVal + b.toVal) =
      step.e_lo.toVal - (step.e_hi.toVal + a.lo.toVal + b.lo.toVal)
  simp only [DoubleDouble.toVal, result_hi, result_lo]
  -- Goal: hi_out + lo_out - (a.hi + a.lo + b.hi + b.lo) = e_lo - (e_hi + a.lo + b.lo)
  -- LHS via h_final: s_hi + e_lo - (a.hi + a.lo + b.hi + b.lo)
  -- s_hi = a.hi + b.hi - e_hi by h_hi
  -- LHS = (a.hi + b.hi - e_hi) + e_lo - (a.hi + a.lo + b.hi + b.lo)
  --     = e_lo - e_hi - a.lo - b.lo  ✓
  linarith [h_final, h_hi]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_add` result.**

The output `⟨hi_out, lo_out⟩` is normalized via the final TwoSum identity. -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  isNormalized_of_value_witness (R := R)
    step.s_hi step.e_lo step.hi_out step.lo_out step.hhi_out step.hlo_out_exact

omit [RModeConj R] [RModeIdem R] in
/-- **Error bound for `dd_add`.**

Given normal-range or exact-zero hypotheses on each lo-channel intermediate
sum, the dd_add result deviates from the true value `a + b` by at most
`η · (|e_hi + a.lo| + |e_lo_partial + b.lo|)`. The two TwoSum steps
contribute zero error (exact); the bound is entirely from the two rounded
adds in the lo channel.

For normalized inputs this bound is roughly `η²·|a + b|` because each lo is
already at the η-scale of the corresponding hi. -/
theorem error_bound
    (h1 : isNormalRange ((step.e_hi.toVal : R) + a.lo.toVal) ∨
          (step.e_hi.toVal : R) + a.lo.toVal = 0)
    (h2 : isNormalRange ((step.e_lo_partial.toVal : R) + b.lo.toVal) ∨
          (step.e_lo_partial.toVal : R) + b.lo.toVal = 0) :
    |step.result.toVal (R := R) - (a.toVal + b.toVal)| ≤
      η * (|(step.e_hi.toVal : R) + a.lo.toVal| +
           |(step.e_lo_partial.toVal : R) + b.lo.toVal|) := by
  -- Per-step rounding bounds
  have h_step1 := KahanSum.fpAdd_error_or_zero (R := R)
    step.e_hi a.lo step.e_lo_partial step.he_lo_partial h1
  have h_step2 := KahanSum.fpAdd_error_or_zero (R := R)
    step.e_lo_partial b.lo step.e_lo step.he_lo h2
  -- Use the exact value identity: result - (a+b) = e_lo - (e_hi + a.lo + b.lo)
  have h_id := step.result_value
  -- Rewrite goal RHS into the two rounding-error pieces
  have h_split : step.result.toVal (R := R) - (a.toVal + b.toVal) =
      (step.e_lo.toVal - (step.e_lo_partial.toVal + b.lo.toVal)) +
      (step.e_lo_partial.toVal - (step.e_hi.toVal + a.lo.toVal)) := by
    linarith [h_id]
  rw [h_split]
  calc |(step.e_lo.toVal - (step.e_lo_partial.toVal + b.lo.toVal)) +
        (step.e_lo_partial.toVal - (step.e_hi.toVal + a.lo.toVal))|
      ≤ |(step.e_lo.toVal : R) - (step.e_lo_partial.toVal + b.lo.toVal)| +
        |(step.e_lo_partial.toVal : R) - (step.e_hi.toVal + a.lo.toVal)| :=
        abs_add_le _ _
    _ ≤ η * |(step.e_lo_partial.toVal : R) + b.lo.toVal| +
        η * |(step.e_hi.toVal : R) + a.lo.toVal| := by
        gcongr
    _ = η * (|(step.e_hi.toVal : R) + a.lo.toVal| +
             |(step.e_lo_partial.toVal : R) + b.lo.toVal|) := by ring

end DDAddStep

/-! ## Constructors

Two layers of API for building a `DDAddStep`:

- `DDAddStep.ofWitnesses` is the structural rename of the underlying record
  constructor — same arguments, named for clarity at call sites. Use this
  when you've already produced all six FP values and both TwoSum identities
  (e.g., from a prior `twoSum_exact` or `twoSum_6op` application).

- `DDAddStep.exists_via_twoSum` is the smart constructor: caller supplies
  the four "natively computed" FP values (`s_hi`, `e_lo_partial`, `e_lo`,
  `hi_out`) plus their addition equalities, plus `e_hi` with its TwoSum
  identity (typically obtained from `twoSum_exact` on the hi parts), plus
  nonzero-significand witnesses for the final renormalize. The `lo_out`
  value and the second TwoSum identity are produced internally via
  `twoSum_exact`. -/

namespace DDAddStep

variable {a b : DoubleDouble}

/-- Structural constructor for `DDAddStep`. Same fields as the record
    literal `⟨...⟩`, exposed as a named function for documentation. -/
@[inline]
def ofWitnesses
    (s_hi e_hi e_lo_partial e_lo hi_out lo_out : FiniteFp)
    (hs_hi : a.hi + b.hi = (s_hi : Fp))
    (he_hi_exact : (s_hi.toVal : R) + e_hi.toVal = a.hi.toVal + b.hi.toVal)
    (he_lo_partial : e_hi + a.lo = (e_lo_partial : Fp))
    (he_lo : e_lo_partial + b.lo = (e_lo : Fp))
    (hhi_out : s_hi + e_lo = (hi_out : Fp))
    (hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = s_hi.toVal + e_lo.toVal) :
    DDAddStep (R := R) a b :=
  { s_hi, hs_hi, e_hi, he_hi_exact, e_lo_partial, he_lo_partial,
    e_lo, he_lo, hi_out, hhi_out, lo_out, hlo_out_exact }

omit [RModeIdem R] in
/-- **Smart constructor: lift FP-computation witnesses into a `DDAddStep`.**

The caller supplies the runtime-computed FP values and addition equalities
for every step except the final TwoSum's `lo_out`, which is discharged
internally via `twoSum_exact (R := R) s_hi e_lo` (requires `0 < s_hi.m`,
`0 < e_lo.m`).

The `e_hi` argument is concrete (caller's runtime value); its TwoSum
identity `he_hi_exact` is typically obtained from a prior
`obtain ⟨e_hi, he_hi_exact⟩ := twoSum_exact ... s_hi hs_hi`. The result is
existential because the constructed `lo_out` is itself a TwoSum witness. -/
theorem exists_via_finalTwoSum
    (s_hi e_hi e_lo_partial e_lo hi_out : FiniteFp)
    (hs_hi : a.hi + b.hi = (s_hi : Fp))
    (he_hi_exact : (s_hi.toVal : R) + e_hi.toVal = a.hi.toVal + b.hi.toVal)
    (he_lo_partial : e_hi + a.lo = (e_lo_partial : Fp))
    (he_lo : e_lo_partial + b.lo = (e_lo : Fp))
    (hhi_out : s_hi + e_lo = (hi_out : Fp))
    (hs_hi_nz : 0 < s_hi.m) (he_lo_nz : 0 < e_lo.m) :
    ∃ step : DDAddStep (R := R) a b,
      step.s_hi = s_hi ∧ step.e_hi = e_hi ∧
      step.e_lo_partial = e_lo_partial ∧ step.e_lo = e_lo ∧
      step.hi_out = hi_out := by
  obtain ⟨lo_out, hlo_out_exact⟩ :=
    twoSum_exact (R := R) s_hi e_lo hs_hi_nz he_lo_nz hi_out hhi_out
  refine ⟨ofWitnesses (R := R) s_hi e_hi e_lo_partial e_lo hi_out lo_out
            hs_hi he_hi_exact he_lo_partial he_lo hhi_out hlo_out_exact,
          ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end DDAddStep

end DDAdd

/-! ## `dd_mul`: multiplication of two DoubleDoubles

Standard FMA-based 7-op DD multiplication (Joldes-Muller-Popescu-Tucker
*DWTimesDW3* style, with TwoSum instead of Fast2Sum on the final renormalize
to avoid the magnitude precondition):

```
(p_hi, p_lo)     := TwoProduct(a.hi, b.hi)         -- exact via FMA
t1               := round(a.hi · b.lo + p_lo)      -- 1 FMA
c                := round(a.lo · b.hi + t1)        -- 1 FMA
(hi_out, lo_out) := TwoSum(p_hi, c)                -- exact
return ⟨hi_out, lo_out⟩
```

The two TwoProduct/TwoSum identities are exact, so the only error sources
are the two FMAs in the lo channel plus the omitted `a.lo · b.lo` term.

```
result.toVal − a · b
  = (c − (a.lo · b.hi + t1))           -- δ from second FMA
  + (t1 − (a.hi · b.lo + p_lo))        -- δ from first FMA
  − a.lo · b.lo                        -- omitted cross term
```

For normalized inputs all three terms are `O(η²·|a · b|)`, giving the
classical DD multiplication bound. -/

section DDMul

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one execution of double-double multiplication.

Bundles the FiniteFp results of every rounding step plus the two exactness
identities (TwoProduct on hi parts, TwoSum on the final renormalize). -/
structure DDMulStep (a b : DoubleDouble) where
  /-- TwoProduct on the hi parts: rounded product. -/
  p_hi : FiniteFp
  hp_hi : a.hi * b.hi = (p_hi : Fp)
  /-- TwoProduct on the hi parts: error. -/
  p_lo : FiniteFp
  hp_exact : (p_hi.toVal : R) + p_lo.toVal = a.hi.toVal * b.hi.toVal
  /-- First lo-channel FMA: `t1 = round(a.hi · b.lo + p_lo)`. -/
  t1 : FiniteFp
  ht1 : fpFMAFinite a.hi b.lo p_lo = (t1 : Fp)
  /-- Second lo-channel FMA: `c = round(a.lo · b.hi + t1)`. -/
  c : FiniteFp
  hc : fpFMAFinite a.lo b.hi t1 = (c : Fp)
  /-- Final TwoSum: rounded sum. -/
  hi_out : FiniteFp
  hhi_out : p_hi + c = (hi_out : Fp)
  /-- Final TwoSum: error (the new lo). -/
  lo_out : FiniteFp
  hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = p_hi.toVal + c.toVal

namespace DDMulStep

variable {a b : DoubleDouble} (step : DDMulStep (R := R) a b)

/-- The `DoubleDouble` produced by the multiplication step. -/
def result : DoubleDouble := ⟨step.hi_out, step.lo_out⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_hi : step.result.hi = step.hi_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_lo : step.result.lo = step.lo_out := rfl

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_mul`.**

The result deviates from the true product `a · b` by exactly the sum of two
FMA rounding errors plus the omitted cross term `−a.lo · b.lo`. -/
theorem result_value :
    step.result.toVal (R := R) - a.toVal * b.toVal =
      (step.c.toVal - (a.lo.toVal * b.hi.toVal + step.t1.toVal))
      + (step.t1.toVal - (a.hi.toVal * b.lo.toVal + step.p_lo.toVal))
      - a.lo.toVal * b.lo.toVal := by
  have h_final : (step.hi_out.toVal : R) + step.lo_out.toVal =
      step.p_hi.toVal + step.c.toVal := step.hlo_out_exact
  have h_prod : (step.p_hi.toVal : R) + step.p_lo.toVal =
      a.hi.toVal * b.hi.toVal := step.hp_exact
  show step.result.toVal (R := R) - a.toVal * b.toVal =
      (step.c.toVal - (a.lo.toVal * b.hi.toVal + step.t1.toVal))
      + (step.t1.toVal - (a.hi.toVal * b.lo.toVal + step.p_lo.toVal))
      - a.lo.toVal * b.lo.toVal
  simp only [DoubleDouble.toVal, result_hi, result_lo]
  -- LHS via h_final: p_hi + c - (a.hi+a.lo)·(b.hi+b.lo)
  -- p_hi = a.hi·b.hi - p_lo via h_prod
  -- LHS = (a.hi·b.hi - p_lo) + c - a.hi·b.hi - a.hi·b.lo - a.lo·b.hi - a.lo·b.lo
  --     = c - p_lo - a.hi·b.lo - a.lo·b.hi - a.lo·b.lo
  --     = (c - a.lo·b.hi - t1) + (t1 - a.hi·b.lo - p_lo) - a.lo·b.lo  ✓
  nlinarith [h_final, h_prod]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_mul` result.**

The output `⟨hi_out, lo_out⟩` is normalized via the final TwoSum identity. -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  isNormalized_of_value_witness (R := R)
    step.p_hi step.c step.hi_out step.lo_out step.hhi_out step.hlo_out_exact

omit [RModeConj R] [RModeIdem R] in
/-- **Error bound for `dd_mul`.**

Given normal-range or exact-zero hypotheses on each lo-channel FMA, the
result deviates from `a · b` by at most
`η · (|a.hi·b.lo + p_lo| + |a.lo·b.hi + t1|) + |a.lo · b.lo|`.
For normalized inputs all three terms are `O(η²·|a·b|)`. -/
theorem error_bound
    (h1 : isNormalRange (a.hi.toVal * b.lo.toVal + (step.p_lo.toVal : R)) ∨
          a.hi.toVal * b.lo.toVal + (step.p_lo.toVal : R) = 0)
    (h2 : isNormalRange (a.lo.toVal * b.hi.toVal + (step.t1.toVal : R)) ∨
          a.lo.toVal * b.hi.toVal + (step.t1.toVal : R) = 0) :
    |step.result.toVal (R := R) - a.toVal * b.toVal| ≤
      η * (|a.hi.toVal * b.lo.toVal + (step.p_lo.toVal : R)| +
           |a.lo.toVal * b.hi.toVal + (step.t1.toVal : R)|) +
      |a.lo.toVal * b.lo.toVal (R := R)| := by
  -- Per-FMA rounding bounds
  have h_fma1 := HornerFMA.fpFMA_error_or_zero (R := R)
    a.hi b.lo step.p_lo step.t1 step.ht1 h1
  have h_fma2 := HornerFMA.fpFMA_error_or_zero (R := R)
    a.lo b.hi step.t1 step.c step.hc h2
  -- Use the exact value identity
  have h_id := step.result_value
  rw [h_id]
  calc |(step.c.toVal - (a.lo.toVal * b.hi.toVal + step.t1.toVal))
        + (step.t1.toVal - (a.hi.toVal * b.lo.toVal + step.p_lo.toVal))
        - a.lo.toVal * b.lo.toVal|
      ≤ |(step.c.toVal - (a.lo.toVal * b.hi.toVal + step.t1.toVal))
        + (step.t1.toVal - (a.hi.toVal * b.lo.toVal + step.p_lo.toVal))| +
        |a.lo.toVal * b.lo.toVal (R := R)| := abs_sub _ _
    _ ≤ |(step.c.toVal : R) - (a.lo.toVal * b.hi.toVal + step.t1.toVal)| +
        |(step.t1.toVal : R) - (a.hi.toVal * b.lo.toVal + step.p_lo.toVal)| +
        |a.lo.toVal * b.lo.toVal (R := R)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ η * |a.lo.toVal * b.hi.toVal + (step.t1.toVal : R)| +
        η * |a.hi.toVal * b.lo.toVal + (step.p_lo.toVal : R)| +
        |a.lo.toVal * b.lo.toVal (R := R)| := by
        gcongr
    _ = η * (|a.hi.toVal * b.lo.toVal + (step.p_lo.toVal : R)| +
             |a.lo.toVal * b.hi.toVal + (step.t1.toVal : R)|) +
        |a.lo.toVal * b.lo.toVal (R := R)| := by ring

end DDMulStep

/-! ### Constructors -/

namespace DDMulStep

variable {a b : DoubleDouble}

/-- Structural constructor for `DDMulStep`. Same fields as the record
    literal, exposed as a named function for documentation. -/
@[inline]
def ofWitnesses
    (p_hi p_lo t1 c hi_out lo_out : FiniteFp)
    (hp_hi : a.hi * b.hi = (p_hi : Fp))
    (hp_exact : (p_hi.toVal : R) + p_lo.toVal = a.hi.toVal * b.hi.toVal)
    (ht1 : fpFMAFinite a.hi b.lo p_lo = (t1 : Fp))
    (hc : fpFMAFinite a.lo b.hi t1 = (c : Fp))
    (hhi_out : p_hi + c = (hi_out : Fp))
    (hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = p_hi.toVal + c.toVal) :
    DDMulStep (R := R) a b :=
  { p_hi, hp_hi, p_lo, hp_exact, t1, ht1, c, hc,
    hi_out, hhi_out, lo_out, hlo_out_exact }

omit [RModeIdem R] in
/-- Smart constructor: discharges the final-renormalize exactness identity
    via `twoSum_exact`. Caller supplies the runtime-computed FP values
    (`p_hi`, `p_lo`, `t1`, `c`, `hi_out`) plus their addition equalities,
    plus `p_lo`'s TwoProduct identity (typically obtained from
    `twoProduct_exact`), plus nonzero-significand witnesses for the final
    renormalize. -/
theorem exists_via_finalTwoSum
    (p_hi p_lo t1 c hi_out : FiniteFp)
    (hp_hi : a.hi * b.hi = (p_hi : Fp))
    (hp_exact : (p_hi.toVal : R) + p_lo.toVal = a.hi.toVal * b.hi.toVal)
    (ht1 : fpFMAFinite a.hi b.lo p_lo = (t1 : Fp))
    (hc : fpFMAFinite a.lo b.hi t1 = (c : Fp))
    (hhi_out : p_hi + c = (hi_out : Fp))
    (hp_hi_nz : 0 < p_hi.m) (hc_nz : 0 < c.m) :
    ∃ step : DDMulStep (R := R) a b,
      step.p_hi = p_hi ∧ step.p_lo = p_lo ∧
      step.t1 = t1 ∧ step.c = c ∧ step.hi_out = hi_out := by
  obtain ⟨lo_out, hlo_out_exact⟩ :=
    twoSum_exact (R := R) p_hi c hp_hi_nz hc_nz hi_out hhi_out
  refine ⟨ofWitnesses (R := R) p_hi p_lo t1 c hi_out lo_out
            hp_hi hp_exact ht1 hc hhi_out hlo_out_exact,
          ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end DDMulStep

end DDMul

/-! ## `dd_sub`: subtraction of two DoubleDoubles

Subtraction reduces to addition with the second argument negated:
`dd_sub a b := dd_add a (-b)`. The full machinery of `DDAddStep` —
result, value identity, normalization, error bound, constructors — is
inherited via this reduction.

We ship a convenience abbreviation `DDSubStep` plus restated value and
error theorems that fold `(-b).toVal = -b.toVal` etc. for ergonomic
call sites. -/

section DDSub

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one execution of double-double subtraction.

Definitionally `DDAddStep R a (-b)`: subtraction is the addition of the
negated second argument. All `DDAddStep` API is reusable via this
reduction. -/
@[reducible]
def DDSubStep (a b : DoubleDouble) : Type := DDAddStep (R := R) a (-b)

namespace DDSubStep

variable {a b : DoubleDouble} (step : DDSubStep (R := R) a b)

/-- The `DoubleDouble` produced by the subtraction step. -/
def result : DoubleDouble := DDAddStep.result step

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_hi : step.result.hi = step.hi_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_lo : step.result.lo = step.lo_out := rfl

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_sub`.**

Folded form of `DDAddStep.result_value` with `(-b).toVal = -b.toVal`
substituted: the result deviates from `a − b` by exactly the difference
between the computed `e_lo` and the ideal `e_hi + a.lo − b.lo`. -/
theorem result_value :
    step.result.toVal (R := R) - (a.toVal - b.toVal) =
      step.e_lo.toVal - (step.e_hi.toVal + a.lo.toVal - b.lo.toVal) := by
  have h := DDAddStep.result_value (R := R) (a := a) (b := -b) step
  simp only [DoubleDouble.toVal_neg, DoubleDouble.neg_lo,
             FiniteFp.toVal_neg_eq_neg] at h
  -- Unfold step.result to (DDAddStep.result step) for linarith to see h
  show (DDAddStep.result step).toVal (R := R) - (a.toVal - b.toVal) =
      step.e_lo.toVal - (step.e_hi.toVal + a.lo.toVal - b.lo.toVal)
  linarith [h]

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_sub` result.** -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  DDAddStep.result_isNormalized (R := R) (a := a) (b := -b) step

omit [RModeConj R] [RModeIdem R] in
/-- **Error bound for `dd_sub`.**

Folded form of `DDAddStep.error_bound`: under per-step normal-range or
exact-zero hypotheses, `|result − (a − b)| ≤ η · (|e_hi + a.lo|
+ |e_lo_partial − b.lo|)`. Only the second hypothesis picks up the
negation — the first lo-channel FMA `e_hi + a.lo` is unchanged because
`a` is not negated. -/
theorem error_bound
    (h1 : isNormalRange ((step.e_hi.toVal : R) + a.lo.toVal) ∨
          (step.e_hi.toVal : R) + a.lo.toVal = 0)
    (h2 : isNormalRange ((step.e_lo_partial.toVal : R) - b.lo.toVal) ∨
          (step.e_lo_partial.toVal : R) - b.lo.toVal = 0) :
    |step.result.toVal (R := R) - (a.toVal - b.toVal)| ≤
      η * (|(step.e_hi.toVal : R) + a.lo.toVal| +
           |(step.e_lo_partial.toVal : R) - b.lo.toVal|) := by
  -- Translate h2 to (-b).lo form so DDAddStep.error_bound applies
  have h2' : isNormalRange ((step.e_lo_partial.toVal : R) + (-b).lo.toVal) ∨
             (step.e_lo_partial.toVal : R) + (-b).lo.toVal = 0 := by
    simpa [DoubleDouble.neg_lo, FiniteFp.toVal_neg_eq_neg, sub_eq_add_neg] using h2
  have h := DDAddStep.error_bound (R := R) (a := a) (b := -b) step h1 h2'
  -- Unfold (-b)'s toVals; `← sub_eq_add_neg` then folds `_ + -_` back to `_ - _`
  simp only [DoubleDouble.toVal_neg, DoubleDouble.neg_lo,
             FiniteFp.toVal_neg_eq_neg, ← sub_eq_add_neg] at h
  show |(DDAddStep.result step).toVal (R := R) - (a.toVal - b.toVal)| ≤ _
  exact h

end DDSubStep

end DDSub

/-! ## `dd_div`: division of two DoubleDoubles

One-iteration Newton-style refinement (QD-library `dd_div` shape, with TwoSum
on the final accumulation):

```
q1                := round(a.hi / b.hi)            -- 1 div
prod              := dd_mul(⟨q1, 0⟩, b)            -- DD product q1·b (DDMulStep)
residual          := dd_sub(a, prod.result)        -- DD residual r ≈ a − q1·b
q2                := round(residual.hi / b.hi)     -- 1 div, correction
(hi_out, lo_out)  := TwoSum(q1, q2)                -- exact final accumulate
return ⟨hi_out, lo_out⟩
```

Mathematical identity (informal): if `r = a − q1·b` is the true residual, then
`a/b = q1 + r/b`. Computing `q2 ≈ r.hi / b.hi ≈ r/b` gives
`q1 + q2 ≈ a/b`. With one Newton iteration the relative error is roughly
`η²·|a/b|`; a second iteration would give `η³`.

Stage D1 (this section): structure, value identity, normalization,
constructor. Stage D2 will add the quantitative `|result · b − a| ≤ ε`
bound under normal-range hypotheses. -/

section DDDiv

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R]

/-- Witnesses for one execution of double-double division (single Newton
iteration).

The structure is genuinely *dependent*: `prod` references `q1`, `residual`
references `prod.result`, and so on. Each field bundles the runtime FP
witnesses for one stage of the pipeline. -/
structure DDDivStep (a b : DoubleDouble) where
  /-- Initial division: `q1 = round(a.hi / b.hi)`. -/
  q1 : FiniteFp
  hq1 : a.hi / b.hi = (q1 : Fp)
  /-- DD product `q1 · b`. -/
  prod : DDMulStep (R := R) (DoubleDouble.ofFiniteFp q1) b
  /-- DD residual `a − q1·b`. -/
  residual : DDSubStep (R := R) a prod.result
  /-- Correction division: `q2 = round(residual.hi / b.hi)`. -/
  q2 : FiniteFp
  hq2 : residual.result.hi / b.hi = (q2 : Fp)
  /-- Final TwoSum on `(q1, q2)`: rounded sum. -/
  hi_out : FiniteFp
  hhi_out : q1 + q2 = (hi_out : Fp)
  /-- Final TwoSum: error (the new lo). -/
  lo_out : FiniteFp
  hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = q1.toVal + q2.toVal

namespace DDDivStep

variable {a b : DoubleDouble} (step : DDDivStep (R := R) a b)

/-- The `DoubleDouble` produced by the division step. -/
def result : DoubleDouble := ⟨step.hi_out, step.lo_out⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_hi : step.result.hi = step.hi_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [RMode R] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
@[simp] theorem result_lo : step.result.lo = step.lo_out := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact value identity for `dd_div`.**

The result equals `q1 + q2` exactly via the final TwoSum. The relation to
`a/b` is captured separately by the quantitative `error_bound` (Stage D2). -/
theorem result_value :
    step.result.toVal (R := R) = step.q1.toVal + step.q2.toVal := by
  show (step.hi_out.toVal : R) + step.lo_out.toVal = step.q1.toVal + step.q2.toVal
  exact step.hlo_out_exact

omit [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Normalization of the `dd_div` result.**

The output `⟨hi_out, lo_out⟩` is normalized via the final TwoSum identity. -/
theorem result_isNormalized :
    step.result.IsNormalized (R := R) :=
  isNormalized_of_value_witness (R := R)
    step.q1 step.q2 step.hi_out step.lo_out step.hhi_out step.hlo_out_exact

/-! ### Quantitative bound (Stage D2)

The mathematical correctness of one Newton iteration:
`a/b = q1 + r/b` where `r = a − q1·b` is the true residual. Computing
`q2 ≈ r/b` then gives `q1 + q2 ≈ a/b`.

The key bound is on `result · b − a` (then `result − a/b` follows by
dividing by `b`). The decomposition is exact:

```
result · b − a  =  −δ_mul                          -- DD-mul of q1·b
                 + δ_sub                            -- DD-sub of a − q1·b
                 − residual.lo                      -- residual hi/lo split
                 + (q2 · b.hi − residual.hi)        -- division rounding
                 + q2 · b.lo                        -- b hi/lo split
```

For normalized inputs all five terms are O(η²·|a|), giving the classical
`O(η²)` DD-div bound on `|result − a/b|`. The shipped form is the exact
identity; a quantitative bound is built on top by plugging the named
sub-bounds (DDMulStep.error_bound, DDSubStep.error_bound, division
rounding, normalization for residual.lo). -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [RMode R]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Coarse residual identity.**

`result · b − a = q2 · b − r` where `r = a − q1·b` is the true residual.
Trivial corollary of `result_value`. -/
theorem result_minus_target :
    step.result.toVal (R := R) * b.toVal - a.toVal =
      step.q2.toVal * b.toVal - (a.toVal - step.q1.toVal * b.toVal) := by
  rw [step.result_value]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [RMode R]
    [RoundIntSigMSound R] [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Exact 5-term decomposition of `result · b − a`.**

Each term is the contribution of one rounding step in the dd_div pipeline:
the DD-mul of `q1·b`, the DD-sub of the residual, the hi/lo split of the
residual (low part dropped before correction division), the FP-division
rounding, and the hi/lo split of `b` (low part dropped on multiply-back).
For Stage D2b, plug in piecewise bounds (`DDMulStep.error_bound`,
`DDSubStep.error_bound`, `fpDiv` rounding, normalization). -/
theorem result_residual_decomposition :
    step.result.toVal (R := R) * b.toVal - a.toVal =
      -(step.prod.result.toVal - step.q1.toVal * b.toVal)
      + (step.residual.result.toVal - (a.toVal - step.prod.result.toVal))
      - step.residual.result.lo.toVal
      + (step.q2.toVal * b.hi.toVal - step.residual.result.hi.toVal)
      + step.q2.toVal * b.lo.toVal := by
  have h_result := step.result_value
  have hb : (b.toVal : R) = b.hi.toVal + b.lo.toVal := rfl
  have hr : step.residual.result.toVal (R := R) =
      step.residual.result.hi.toVal + step.residual.result.lo.toVal := rfl
  show step.result.toVal (R := R) * b.toVal - a.toVal = _
  rw [h_result, hb, hr]
  ring

omit [FloorRing R] [RMode R] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] [RModeIdem R] in
/-- **Bound on `|result · b − a|`** in terms of named per-step pieces.

Five sources of error: the two DD-arithmetic deviations (mul/sub), the
two hi/lo splits (residual and `b`), and the FP-division rounding on `q2`.
The hypothesis form is "magnitude of each error piece" — no normal-range
preconditions; users compose this with `DDMulStep.error_bound`,
`DDSubStep.error_bound`, etc. for concrete instantiations.

Note: the user supplies the per-piece bounds rather than the bound being
auto-derived, so this works in any rounding-mode regime. -/
theorem result_residual_bound
    (mulErr subErr : R)
    (hMul : |step.prod.result.toVal (R := R) - step.q1.toVal * b.toVal| ≤ mulErr)
    (hSub : |step.residual.result.toVal (R := R) -
              (a.toVal - step.prod.result.toVal)| ≤ subErr) :
    |step.result.toVal (R := R) * b.toVal - a.toVal| ≤
      mulErr + subErr + |step.residual.result.lo.toVal (R := R)|
      + |step.q2.toVal * b.hi.toVal - step.residual.result.hi.toVal (R := R)|
      + |step.q2.toVal * b.lo.toVal (R := R)| := by
  rw [step.result_residual_decomposition]
  -- Name the five error pieces
  set e1 := step.prod.result.toVal (R := R) - step.q1.toVal * b.toVal
  set e2 := step.residual.result.toVal (R := R) -
            (a.toVal - step.prod.result.toVal)
  set e3 := step.residual.result.lo.toVal (R := R)
  set e4 := step.q2.toVal * b.hi.toVal - step.residual.result.hi.toVal (R := R)
  set e5 := step.q2.toVal * b.lo.toVal (R := R)
  -- Goal: |-e1 + e2 - e3 + e4 + e5| ≤ mulErr + subErr + |e3| + |e4| + |e5|
  -- Build triangle inequality bound by repeated abs_add_le
  have hkey : (-e1 + e2 - e3 + e4 + e5 : R) = -e1 + e2 + (-e3) + e4 + e5 := by ring
  rw [hkey]
  have h1 : |(-e1 + e2 + -e3 + e4 + e5 : R)|
      ≤ |(-e1 + e2 + -e3 + e4 : R)| + |e5| := abs_add_le _ _
  have h2 : |(-e1 + e2 + -e3 + e4 : R)|
      ≤ |(-e1 + e2 + -e3 : R)| + |e4| := abs_add_le _ _
  have h3 : |(-e1 + e2 + -e3 : R)|
      ≤ |(-e1 + e2 : R)| + |(-e3 : R)| := abs_add_le _ _
  have h4 : |(-e1 + e2 : R)|
      ≤ |(-e1 : R)| + |e2| := abs_add_le _ _
  have hne1 : |(-e1 : R)| = |e1| := abs_neg _
  have hne3 : |(-e3 : R)| = |e3| := abs_neg _
  linarith [hMul, hSub, abs_nonneg e3, abs_nonneg e4, abs_nonneg e5]

end DDDivStep

/-! ### Constructor -/

namespace DDDivStep

variable {a b : DoubleDouble}

/-- Structural constructor for `DDDivStep`. The structure's dependent fields
    (`prod` referencing `q1`, `residual` referencing `prod.result`) make
    constructor calls naturally pipelined. -/
@[inline]
def ofWitnesses
    (q1 : FiniteFp)
    (hq1 : a.hi / b.hi = (q1 : Fp))
    (prod : DDMulStep (R := R) (DoubleDouble.ofFiniteFp q1) b)
    (residual : DDSubStep (R := R) a prod.result)
    (q2 : FiniteFp)
    (hq2 : residual.result.hi / b.hi = (q2 : Fp))
    (hi_out : FiniteFp)
    (hhi_out : q1 + q2 = (hi_out : Fp))
    (lo_out : FiniteFp)
    (hlo_out_exact : (hi_out.toVal : R) + lo_out.toVal = q1.toVal + q2.toVal) :
    DDDivStep (R := R) a b :=
  { q1, hq1, prod, residual, q2, hq2, hi_out, hhi_out, lo_out, hlo_out_exact }

omit [RModeIdem R] in
/-- Smart constructor: discharges the final TwoSum exactness via
    `twoSum_exact`. Caller supplies `q1`, the DD-product `prod`, the DD-residual
    `residual`, `q2`, plus the final TwoSum's hi result and the
    nonzero-significand hypotheses. The `lo_out` and its exactness identity
    are produced internally. -/
theorem exists_via_finalTwoSum
    (q1 : FiniteFp) (hq1 : a.hi / b.hi = (q1 : Fp))
    (prod : DDMulStep (R := R) (DoubleDouble.ofFiniteFp q1) b)
    (residual : DDSubStep (R := R) a prod.result)
    (q2 : FiniteFp) (hq2 : residual.result.hi / b.hi = (q2 : Fp))
    (hi_out : FiniteFp) (hhi_out : q1 + q2 = (hi_out : Fp))
    (hq1_nz : 0 < q1.m) (hq2_nz : 0 < q2.m) :
    ∃ step : DDDivStep (R := R) a b,
      step.q1 = q1 ∧ step.q2 = q2 ∧ step.hi_out = hi_out := by
  obtain ⟨lo_out, hlo_out_exact⟩ :=
    twoSum_exact (R := R) q1 q2 hq1_nz hq2_nz hi_out hhi_out
  refine ⟨ofWitnesses (R := R) q1 hq1 prod residual q2 hq2
            hi_out hhi_out lo_out hlo_out_exact,
          ?_, ?_, ?_⟩ <;> rfl

/-! ### Stage D2b: auto-quantitative bound

Combines `DDMulStep.error_bound` (specialised to `ofFiniteFp q1` so `a.lo = 0`,
collapsing the `a.lo · b.hi + t1` and `a.lo · b.lo` pieces) with
`DDSubStep.error_bound` and `result_residual_bound` to produce a fully-derived
five-term inequality. The user supplies four normal-range / exact-zero
hypotheses (one per intermediate rounded step on the lo channel of the DD
multiply and DD subtract) and gets back a closed-form bound. -/

omit [RModeConj R] [RModeIdem R] in
/-- **Auto-quantitative `dd_div` bound.**

Five-term decomposition of `|result · b − a|` with the DD-mul and DD-sub
deviations *automatically* bounded via their respective `error_bound`
theorems. The remaining three terms (residual hi/lo split, FP-division
rounding, b hi/lo split) are exposed verbatim as caller-bounded magnitudes.

For normalized inputs, each of the five terms is `O(η²·|a|)`, giving the
classical Newton-iteration `O(η²·|a/b|)` accuracy after dividing through
by `|b|`. -/
theorem error_bound (step : DDDivStep (R := R) a b)
    (h_mul_1 : isNormalRange ((step.q1.toVal : R) * b.lo.toVal +
                              step.prod.p_lo.toVal) ∨
               (step.q1.toVal : R) * b.lo.toVal + step.prod.p_lo.toVal = 0)
    (h_mul_2 : isNormalRange ((step.prod.t1.toVal : R)) ∨
               (step.prod.t1.toVal : R) = 0)
    (h_sub_1 : isNormalRange ((step.residual.e_hi.toVal : R) + a.lo.toVal) ∨
               (step.residual.e_hi.toVal : R) + a.lo.toVal = 0)
    (h_sub_2 : isNormalRange ((step.residual.e_lo_partial.toVal : R) -
                              step.prod.result.lo.toVal) ∨
               (step.residual.e_lo_partial.toVal : R) -
                  step.prod.result.lo.toVal = 0) :
    |step.result.toVal (R := R) * b.toVal - a.toVal| ≤
      η * (|(step.q1.toVal : R) * b.lo.toVal + step.prod.p_lo.toVal| +
           |(step.prod.t1.toVal : R)|)
      + η * (|(step.residual.e_hi.toVal : R) + a.lo.toVal| +
             |(step.residual.e_lo_partial.toVal : R) - step.prod.result.lo.toVal|)
      + |step.residual.result.lo.toVal (R := R)|
      + |step.q2.toVal * b.hi.toVal - step.residual.result.hi.toVal (R := R)|
      + |step.q2.toVal * b.lo.toVal (R := R)| := by
  -- Apply DDMulStep.error_bound on step.prod, then collapse the a.lo = 0 pieces
  have h_mul_raw := step.prod.error_bound (R := R)
    (by
      -- (ofFiniteFp q1).hi = q1, so the hypothesis matches after simp
      simpa [DoubleDouble.ofFiniteFp_hi] using h_mul_1)
    (by
      -- (ofFiniteFp q1).lo = 0, so 0·b.hi + t1 = t1
      have : ((DoubleDouble.ofFiniteFp step.q1).lo.toVal : R) * b.hi.toVal +
             step.prod.t1.toVal = step.prod.t1.toVal := by
        simp [DoubleDouble.ofFiniteFp_lo]
      rw [this]; exact h_mul_2)
  -- Simplify h_mul_raw via (ofFiniteFp q1).hi = q1 and .lo = 0
  have h_mul : |step.prod.result.toVal (R := R) - step.q1.toVal * b.toVal| ≤
      η * (|(step.q1.toVal : R) * b.lo.toVal + step.prod.p_lo.toVal| +
           |(step.prod.t1.toVal : R)|) := by
    have h_aval : ((DoubleDouble.ofFiniteFp step.q1).toVal : R) = step.q1.toVal := by
      simp [DoubleDouble.toVal_ofFiniteFp]
    rw [h_aval] at h_mul_raw
    have h_alo : ((DoubleDouble.ofFiniteFp step.q1).lo.toVal : R) = 0 := by
      simp [DoubleDouble.ofFiniteFp_lo]
    have h_ahi : ((DoubleDouble.ofFiniteFp step.q1).hi.toVal : R) = step.q1.toVal := by
      simp [DoubleDouble.ofFiniteFp_hi]
    rw [h_alo, h_ahi] at h_mul_raw
    simp only [zero_mul, zero_add, abs_zero, add_zero] at h_mul_raw
    exact h_mul_raw
  -- Apply DDSubStep.error_bound on step.residual
  have h_sub := step.residual.error_bound (R := R) h_sub_1 h_sub_2
  -- Compose via result_residual_bound
  exact step.result_residual_bound (R := R) _ _ h_mul h_sub

end DDDivStep

end DDDiv

-- `dd_sqrt` lives in `Flean/Operations/DoubleDoubleSqrt.lean` (separate file
-- to keep DoubleDouble.lean's elaboration tractable).
