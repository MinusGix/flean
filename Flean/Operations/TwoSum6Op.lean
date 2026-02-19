import Flean.Operations.TwoSum
import Flean.Operations.Fast2Sum

/-! # Branchless 6-Operation 2Sum (Knuth/Møller)

The 6-op 2Sum algorithm computes the error-free transformation of a + b
without requiring an ordering assumption on |a| vs |b|:

```
s  = a ⊕ b        -- rounded sum
bv = s ⊖ a        -- "b_virtual"
av = s ⊖ bv       -- "a_virtual"
br = b ⊖ bv       -- "b_roundoff"
ar = a ⊖ av       -- "a_roundoff"
t  = ar ⊕ br      -- error term
```

The main theorem `twoSum_6op` proves `s + t = a + b` exactly.

This only holds for **nearest** rounding modes. For directed modes (toward zero,
toward ±∞), the splitting property `av + bv = s` can fail.

TODO: formal counterexample for directed rounding modes (e.g., roundTowardZero
with p=3, a=7, b=1: s=8, bv=round(8-7)=1, av=round(8-1)=7, av+bv=8=s works,
but try a=15, b=1: s=16, bv=round(16-15)=1, av=round(16-1)=14, av+bv=15≠16).
-/

section TwoSum6Op

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Helpers -/

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
/-- Extract toVal equality from Fp.finite equality. -/
private theorem toVal_of_fp_eq (x y : FiniteFp) (h : (x : Fp) = (y : Fp)) :
    x.toVal (R := R) = y.toVal := by
  have := Fp.finite.inj h; subst this; rfl

omit [FloorRing R] in
/-- When the exact sum of two FiniteFp is zero, their fp-addition yields a zero. -/
private theorem fpAddFinite_zero_of_eq_sum [RModeExec] (a b : FiniteFp)
    (hsum : (a.toVal : R) + b.toVal = 0) :
    ∃ f : FiniteFp, a + b = f ∧ f.toVal (R := R) = 0 := by
  have hexact := fpAddFinite_exact_sum R a b
  have hisum_zero : addAlignedSumInt a b = 0 := by
    have h0 : ((addAlignedSumInt a b : ℤ) : R) * (2 : R) ^ (min a.e b.e - prec + 1) = 0 := by
      rw [← hexact]; exact hsum
    rcases mul_eq_zero.mp h0 with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (zpow_pos (by norm_num) _))
  let fz : FiniteFp := ⟨exactCancelSign a.s b.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  refine ⟨fz, ?_, FiniteFp.toVal_isZero rfl⟩
  simp only [add_finite_eq_fpAddFinite]
  exact fpAddFinite_exact_cancel_sign a b hisum_zero

/-! ## Splitting Lemma (positive case via Sterbenz)

When |a| ≥ |b| and both positive, Sterbenz gives bv = s - a exactly.
Then av = round(a) = a by idempotency, so av + bv = s. -/

/-- For positive `a ≥ b`, the 6-op splitting av + bv = s holds because
    s - a is exact by Sterbenz and round(a) = a by idempotency. -/
private theorem splitting_pos (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    (s : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R]
    (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp)) :
    av.toVal (R := R) + bv.toVal = s.toVal ∧
      bv.toVal (R := R) = s.toVal - a.toVal ∧
        av.toVal (R := R) = a.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  -- Step 1: bv = s - a is exact by Sterbenz
  obtain ⟨z, hz_eq, hz_val⟩ :=
    sterbenz_sub_sa (R := R) a b ha hb ha_nz hb_nz hab hsum_ne s hs
  have hbv_val : bv.toVal (R := R) = s.toVal - a.toVal := by
    rw [toVal_of_fp_eq (R := R) bv z (hbv.symm.trans hz_eq)]; exact hz_val
  -- Step 2: av = round(s - bv) = round(s - (s - a)) = round(a) = a
  have hsbv : s.toVal (R := R) - bv.toVal = a.toVal := by linarith
  have hav_val : av.toVal (R := R) = a.toVal := by
    have hav_round : (av : Fp) = ○(s.toVal (R := R) - bv.toVal) := by
      have h0 : s.toVal (R := R) - bv.toVal ≠ 0 := by linarith
      exact hav.symm.trans (fpSubFinite_correct (R := R) s bv h0)
    have : (av : Fp) = Fp.finite a := by
      rw [hav_round, hsbv, RModeIdem.round_idempotent (R := R) a (Or.inl ha)]
    exact toVal_of_fp_eq (R := R) av a this
  exact ⟨by linarith, hbv_val, hav_val⟩

/-! ## Post-splitting: from splitting to s + t = a + b

Given the strong splitting property (bv = s - a exactly, av = a), derive
all remaining exactness properties and the final identity. -/

/-- Helper to get error representability with automatic abs ordering. -/
private theorem error_representable (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s) :
    ∃ t_fp : FiniteFp,
      (t_fp.s = false ∨ 0 < t_fp.m) ∧
        (t_fp.toVal : R) = (a.toVal : R) + b.toVal - s.toVal := by
  rcases le_or_gt |b.toVal (R := R)| |a.toVal| with hab | hab
  · exact add_error_representable_general (R := R) a b ha_nz hb_nz hab hsum_ne s hs
  · have hs' : b + a = s := by
      simp only [add_finite_eq_fpAddFinite] at hs ⊢; rw [fpAddFinite_comm]; exact hs
    obtain ⟨t, ht_valid, ht_eq⟩ := add_error_representable_general (R := R) b a
      hb_nz ha_nz (le_of_lt hab) (by rwa [add_comm]) s hs'
    exact ⟨t, ht_valid, by rw [ht_eq]; ring⟩

/-- 6-op correctness from strong splitting (bv exact, av = a).

When `bv.toVal = s.toVal - a.toVal` and `av.toVal = a.toVal`, derive
that all subsequent operations are exact and `s + t = a + b`. -/
private theorem twoSum_6op_of_strong_splitting (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv_val : bv.toVal (R := R) = s.toVal - a.toVal)
    (av : FiniteFp) (hav_val : av.toVal (R := R) = a.toVal)
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  -- ar = round(a - av) = round(a - a) = round(0) = 0
  have har_zero : ar.toVal (R := R) = 0 := by
    obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a av
      (by rw [hav_val])
    exact (toVal_of_fp_eq (R := R) ar f (har.symm.trans hf_eq)).trans hf_val
  -- br = round(b - bv) = round(error) = error (representable!)
  have hbr_val : br.toVal (R := R) = b.toVal - bv.toVal := by
    by_cases hbr0 : b.toVal (R := R) - bv.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv
        (by linarith)
      rw [(toVal_of_fp_eq (R := R) br f (hbr.symm.trans hf_eq)).trans hf_val, hbr0]
    · obtain ⟨err, herr_valid, herr_eq⟩ := error_representable (R := R) a b
        ha_nz hb_nz hsum_ne s hs
      have hbr_err : b.toVal (R := R) - bv.toVal = err.toVal := by
        rw [hbv_val, herr_eq]; ring
      have hbr_corr := fpSubFinite_correct (R := R) b bv hbr0
      simp only [sub_eq_fpSub, fpSub_coe_coe] at hbr_corr hbr
      rw [hbr_corr, hbr_err, RModeIdem.round_idempotent (R := R) err herr_valid] at hbr
      exact (toVal_of_fp_eq (R := R) br err hbr.symm).trans hbr_err.symm
  -- ar + br = 0 + (b - bv) = b - (s - a) = a + b - s
  have ht_sum : ar.toVal (R := R) + br.toVal = a.toVal + b.toVal - s.toVal := by
    rw [har_zero, zero_add, hbr_val, hbv_val]; ring
  -- t is exact because a + b - s is representable
  have ht_val : t.toVal (R := R) = ar.toVal + br.toVal := by
    by_cases ht0 : ar.toVal (R := R) + br.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) ar br ht0
      have : (t : Fp) = (f : Fp) := ht.symm.trans hf_eq
      rw [(toVal_of_fp_eq (R := R) t f this).trans hf_val, ht0]
    · obtain ⟨err, herr_valid, herr_eq⟩ := error_representable (R := R) a b
        ha_nz hb_nz hsum_ne s hs
      have ht_err : ar.toVal (R := R) + br.toVal = err.toVal := by
        rw [ht_sum, herr_eq]
      have ht_corr := fpAddFinite_correct (R := R) ar br ht0
      rw [ht_corr, ht_err, RModeIdem.round_idempotent (R := R) err herr_valid] at ht
      exact (toVal_of_fp_eq (R := R) t err ht.symm).trans ht_err.symm
  rw [ht_val, ht_sum]; ring

/-! ## 6-op correctness (positive case via Sterbenz splitting) -/

/-- 6-op 2Sum correctness for positive `a ≥ b`. -/
private theorem twoSum_6op_pos (a b : FiniteFp)
    (ha : a.s = false) (hb : b.s = false)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab : (b.toVal : R) ≤ a.toVal)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
  have hb_pos : (0 : R) < b.toVal := FiniteFp.toVal_pos b hb hb_nz
  have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by linarith
  obtain ⟨_, hbv_val, hav_val⟩ :=
    splitting_pos (R := R) a b ha hb ha_nz hb_nz hab s hs bv hbv av hav
  exact twoSum_6op_of_strong_splitting (R := R) a b ha_nz hb_nz hsum_ne s hs
    bv hbv_val av hav_val br hbr ar har t ht

/-! ## Nonzero sum implies nonzero significand -/

/-- When `a + b ≠ 0`, the rounded sum has a nonzero significand. -/
private theorem nonzero_sum_round_m_pos (a b : FiniteFp)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s) :
    0 < s.m := by
  -- Step 1: grid lower bound — |a + b| ≥ smallestPosSubnormal
  have hexact := fpAddFinite_exact_sum R a b
  set g := min a.e b.e - prec + 1 with g_def
  set isum := addAlignedSumInt a b with isum_def
  have hisum_ne : isum ≠ 0 := by
    intro hzero; apply hsum_ne
    rw [hexact, hzero, Int.cast_zero, zero_mul]
  have hg_ge : g ≥ FloatFormat.min_exp - prec + 1 := by
    have := FiniteFp.valid_min_exp a
    have := FiniteFp.valid_min_exp b
    omega
  have hg_pos : (0 : R) < (2 : R) ^ g := zpow_pos (by norm_num) g
  have hsps := FiniteFp.smallestPosSubnormal_toVal (R := R)
  -- |a + b| ≥ 2^g ≥ 2^(min_exp - prec + 1) = sps.toVal
  have habs_ge : FiniteFp.smallestPosSubnormal.toVal ≤ |a.toVal (R := R) + b.toVal| := by
    rw [hexact, abs_mul, abs_of_pos hg_pos, hsps]
    have : (1 : R) ≤ |(isum : R)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hisum_ne
    calc (2 : R) ^ (FloatFormat.min_exp - prec + 1)
        ≤ (2 : R) ^ g := two_zpow_mono (R := R) hg_ge
      _ = 1 * (2 : R) ^ g := (one_mul _).symm
      _ ≤ |(isum : R)| * (2 : R) ^ g :=
          mul_le_mul_of_nonneg_right this (le_of_lt hg_pos)
  -- Step 2: round maps nonzero grid value to nonzero result
  by_contra hm
  push_neg at hm
  have hm0 : s.m = 0 := by omega
  have hs_zero : s.toVal (R := R) = 0 := FiniteFp.toVal_isZero (show s.isZero from hm0)
  -- Get round equation
  have hs_round : (s : Fp) = ○(a.toVal (R := R) + b.toVal) :=
    hs.symm.trans (fpAddFinite_correct (R := R) a b hsum_ne)
  -- Case split on sign of a + b
  rcases lt_or_gt_of_ne hsum_ne with hlt | hgt
  · -- a + b < 0: round(a+b) ≤ round(-sps) = -sps, so s.toVal ≤ -sps.toVal < 0
    have hle : a.toVal (R := R) + b.toVal ≤ -(FiniteFp.smallestPosSubnormal.toVal) := by
      linarith [abs_of_neg hlt]
    have hsps_ne : (FiniteFp.smallestPosSubnormal.toVal : R) ≠ 0 :=
      ne_of_gt (FiniteFp.smallestPosSubnormal_toVal_pos (R := R))
    have hmono := RModeMono.round_mono (R := R) hle
    rw [← hs_round, RModeConj.round_neg (R := R) _ hsps_ne,
        RModeIdem.round_idempotent (R := R) _ (Or.inl rfl),
        Fp.neg_finite, Fp.finite_le_finite_iff] at hmono
    have := FiniteFp.le_toVal_le R hmono
    rw [FiniteFp.toVal_neg_eq_neg] at this
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]
  · -- a + b > 0: round(a+b) ≥ round(sps) = sps, so s.toVal ≥ sps.toVal > 0
    have hge : FiniteFp.smallestPosSubnormal.toVal ≤ a.toVal (R := R) + b.toVal := by
      linarith [abs_of_pos hgt]
    have hmono := RModeMono.round_mono (R := R) hge
    rw [RModeIdem.round_idempotent (R := R) _ (Or.inl rfl), ← hs_round,
        Fp.finite_le_finite_iff] at hmono
    have := FiniteFp.le_toVal_le R hmono
    linarith [FiniteFp.smallestPosSubnormal_toVal_pos (R := R)]

/-! ## General Splitting Property (Boldo-Muller Proposition 5)

For any two FP numbers `x` and `z = round(x − y)`, the value `x − z`
is always representable. -/

/-- **Weak splitting** (Boldo-Muller Prop 5): `s − round(s − a)` is representable.

Given FP numbers `s` and `a`, and `bv = round(s − a)`, the value `s − bv`
is always representable. This gives `av = round(s − bv) = s − bv` exactly,
hence `av + bv = s`. -/
private theorem sub_round_sub_representable
    (a b : FiniteFp)
    (ha_nz : 0 < a.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeSplit R]
    (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp)) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  have hs_round : ○((a.toVal : R) + b.toVal) = Fp.finite s :=
    (fpAddFinite_correct (R := R) a b hsum_ne).symm.trans hs
  by_cases hsa_zero : s.toVal (R := R) - a.toVal = 0
  · -- s = a, so bv = round(0) is a zero, and s - bv = s, representable
    obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a (by linarith)
    have hbv0 : bv.toVal (R := R) = 0 :=
      (toVal_of_fp_eq (R := R) bv f (hbv.symm.trans hf_eq)).trans hf_val
    have hs_eq_a : s = a := by
      exact FiniteFp.eq_of_toVal_eq' (R := R) (Or.inr (by
        unfold FiniteFp.isZero
        omega)) (by linarith [hsa_zero])
    have hs_nz : 0 < s.m := by simpa [hs_eq_a] using ha_nz
    exact ⟨s, Or.inr hs_nz, by rw [hbv0, sub_zero]⟩
  · have hbv_round : ○((s.toVal : R) - a.toVal) = Fp.finite bv :=
      (fpSubFinite_correct (R := R) s a hsa_zero).symm.trans hbv
    exact RModeSplit.split_s_sub_bv a b s hs_round bv hbv_round

private theorem weak_splitting
    (a b : FiniteFp)
    (ha_nz : 0 < a.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (s : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeSplit R]
    (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp)) :
    av.toVal (R := R) + bv.toVal = s.toVal ∧
      av.toVal (R := R) = s.toVal - bv.toVal := by
  by_cases hsbv : s.toVal (R := R) - bv.toVal = 0
  · -- s = bv, so av = round(0), hence av.toVal = 0
    obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s bv (by linarith)
    have hav_val : av.toVal (R := R) = 0 :=
      (toVal_of_fp_eq (R := R) av f (hav.symm.trans hf_eq)).trans hf_val
    exact ⟨by rw [hav_val, zero_add]; linarith, by rw [hav_val, hsbv]⟩
  · -- s ≠ bv: use representability to show round(s - bv) = s - bv
    obtain ⟨rep, hrep_valid, hrep_val⟩ :=
      sub_round_sub_representable (R := R) a b ha_nz hsum_ne s hs bv hbv
    have hav_corr := fpSubFinite_correct (R := R) s bv hsbv
    simp only [] at hav_corr hav
    rw [hav_corr, ← hrep_val, RModeIdem.round_idempotent (R := R) rep hrep_valid] at hav
    have hav_val := (toVal_of_fp_eq (R := R) av rep hav.symm).trans hrep_val
    exact ⟨by rw [hav_val]; ring, hav_val⟩

/-! ## General 6-op correctness from weak splitting

Given the weak splitting (`av + bv = s`), we show all subsequent
subtractions and the final addition are exact, yielding `s + t = a + b`. -/

/-- 6-op correctness from weak splitting.

Given `av + bv = s` (weak splitting), derive that `ar`, `br`, and `t` are
all computed exactly and `s + t = a + b`. -/
private theorem twoSum_6op_of_weak_splitting (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeSplit R]
    (s : FiniteFp) (hs : a + b = s)
    (bv av : FiniteFp)
    (hbv : s - a = (bv : Fp))
    (hsplit : av.toVal (R := R) + bv.toVal = s.toVal)
    (hav_exact : av.toVal (R := R) = s.toVal - bv.toVal)
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  -- Step 1: a - av is exact (it equals the rounding error of s ⊖ a, negated)
  have har_val : ar.toVal (R := R) = a.toVal - av.toVal := by
    by_cases haav : a.toVal (R := R) - av.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a av (by linarith)
      exact (toVal_of_fp_eq (R := R) ar f (har.symm.trans hf_eq)).trans (hf_val.trans haav.symm)
    · -- a - av = -(s - a - bv) = -(error of s ⊖ a)
      -- error_representable on s + (-a) → bv gives the error
      have hna_nz : 0 < (-a).m := by simp [ha_nz]
      have hsa_ne_val : s.toVal (R := R) - a.toVal ≠ 0 := by
        intro heq
        have hbv0 : bv.toVal (R := R) = 0 := by
          obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a
            (by linarith [heq])
          exact (toVal_of_fp_eq (R := R) bv f (hbv.symm.trans hf_eq)).trans hf_val
        have : av.toVal (R := R) = s.toVal := by rw [hav_exact, hbv0, sub_zero]
        exact haav (by linarith [heq])
      have hsa_ne : s.toVal (R := R) + (-a).toVal ≠ 0 := by
        rwa [FiniteFp.toVal_neg_eq_neg, ← sub_eq_add_neg]
      have hbv' : s + (-a) = (bv : Fp) := by
        -- s - a = bv → s + (-a) = bv since fpSubFinite = fpAddFinite ∘ neg (rfl)
        exact hbv
      have hbv'_comm : (-a) + s = (bv : Fp) := by
        simpa [add_finite_eq_fpAddFinite, fpAddFinite_comm] using hbv'
      obtain ⟨err, herr_valid, herr_eq⟩ := add_error_representable_general_left_nz (R := R)
        (-a) s hna_nz (by simpa [add_comm] using hsa_ne) bv hbv'_comm
      -- err.toVal = s.toVal - a.toVal - bv.toVal, so a - av = -err.toVal
      have hnerr_toVal : (-err).toVal (R := R) = a.toVal - av.toVal := by
        rw [FiniteFp.toVal_neg_eq_neg, hav_exact, herr_eq, FiniteFp.toVal_neg_eq_neg]; ring
      have hnerr_valid : (-err).s = false ∨ 0 < (-err).m := by
        -- Need: err.m > 0 (since err.toVal ≠ 0, as a - av ≠ 0)
        have herr_m_pos : 0 < err.m := by
          by_contra hm; push_neg at hm
          have hm0 : err.m = 0 := by omega
          have : err.toVal (R := R) = 0 :=
            FiniteFp.toVal_isZero (show err.isZero from hm0)
          have : (-err).toVal (R := R) = 0 := by
            rw [FiniteFp.toVal_neg_eq_neg, this, neg_zero]
          exact haav (by rw [← hnerr_toVal, this])
        right; simp [FiniteFp.neg_m]; exact herr_m_pos
      have har_corr := fpSubFinite_correct (R := R) a av haav
      simp only [] at har_corr har
      rw [har_corr, ← hnerr_toVal,
          RModeIdem.round_idempotent (R := R) (-err) hnerr_valid] at har
      exact (toVal_of_fp_eq (R := R) ar (-err) har.symm).trans hnerr_toVal
  -- Step 2: b - bv is exact (from RModeSplit.split_b_sub_bv)
  have hbr_val : br.toVal (R := R) = b.toVal - bv.toVal := by
    by_cases hbbv : b.toVal (R := R) - bv.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv (by linarith)
      exact (toVal_of_fp_eq (R := R) br f (hbr.symm.trans hf_eq)).trans (hf_val.trans hbbv.symm)
    · -- Get round equations for splitting axiom
      have hs_round : ○((a.toVal : R) + b.toVal) = Fp.finite s :=
        (fpAddFinite_correct (R := R) a b hsum_ne).symm.trans hs
      by_cases hsa_zero : s.toVal (R := R) - a.toVal = 0
      · -- s = a, so bv is zero, b - bv = b, representable by idempotency
        obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a (by linarith)
        have hbv0 : bv.toVal (R := R) = 0 :=
          (toVal_of_fp_eq (R := R) bv f (hbv.symm.trans hf_eq)).trans hf_val
        have hbbv' : b.toVal (R := R) - bv.toVal = b.toVal := by rw [hbv0, sub_zero]
        have hbr_corr := fpSubFinite_correct (R := R) b bv hbbv
        rw [hbbv'] at hbr_corr
        rw [hbr_corr, RModeIdem.round_idempotent (R := R) b (Or.inr hb_nz)] at hbr
        exact (toVal_of_fp_eq (R := R) br b hbr.symm).trans hbbv'.symm
      · -- Main case: both nonzero, apply RModeSplit
        have hbv_round : ○((s.toVal : R) - a.toVal) = Fp.finite bv :=
          (fpSubFinite_correct (R := R) s a hsa_zero).symm.trans hbv
        obtain ⟨rep, hrep_valid, hrep_val⟩ :=
          RModeSplit.split_b_sub_bv (R := R) a b s hs_round bv hbv_round
        have hbr_corr := fpSubFinite_correct (R := R) b bv hbbv
        simp only [] at hbr_corr hbr
        rw [hbr_corr, ← hrep_val,
            RModeIdem.round_idempotent (R := R) rep hrep_valid] at hbr
        exact (toVal_of_fp_eq (R := R) br rep hbr.symm).trans hrep_val
  -- Step 3: ar + br = a + b - s (from splitting + exactness)
  have ht_sum : ar.toVal (R := R) + br.toVal = a.toVal + b.toVal - s.toVal := by
    rw [har_val, hbr_val]; linarith
  -- Step 4: t is exact (a + b - s is representable)
  have ht_val : t.toVal (R := R) = ar.toVal + br.toVal := by
    by_cases ht0 : ar.toVal (R := R) + br.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) ar br ht0
      exact (toVal_of_fp_eq (R := R) t f (ht.symm.trans hf_eq)).trans (hf_val.trans ht0.symm)
    · obtain ⟨err, herr_valid, herr_eq⟩ := error_representable (R := R) a b
        ha_nz hb_nz hsum_ne s hs
      have ht_err : ar.toVal (R := R) + br.toVal = err.toVal := by
        rw [ht_sum, herr_eq]
      have ht_corr := fpAddFinite_correct (R := R) ar br ht0
      rw [ht_corr, ht_err, RModeIdem.round_idempotent (R := R) err herr_valid] at ht
      exact (toVal_of_fp_eq (R := R) t err ht.symm).trans ht_err.symm
  rw [ht_val, ht_sum]; ring

/-! ## Main theorem -/

/-- **6-op 2Sum correctness** for arbitrary finite floats.

For any two nonzero finite floats, the branchless 6-operation 2Sum algorithm
produces `(s, t)` satisfying `s + t = a + b` exactly. -/
theorem twoSum_6op (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeSplit R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  -- Handle exact cancellation (a + b = 0) separately
  by_cases hsum_ne : (a.toVal : R) + b.toVal = 0
  · -- When a + b = 0: s is a signed zero, then bv = round(-a) = -a,
    -- av = round(a) = a, ar = 0, br = round(b + a) = 0, t = 0.
    have ha_nz_val : (a.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos a ha_nz
    obtain ⟨sz, hsz_eq, hsz_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) a b hsum_ne
    simp only [add_finite_eq_fpAddFinite] at hs hsz_eq
    have hs_eq : s = sz := Fp.finite.inj (hs.symm.trans hsz_eq)
    subst hs_eq; rw [hsz_val, zero_add]
    -- bv: s - a = round(0 - a) = round(-a) = -round(a) = -a
    have hsa_ne : s.toVal (R := R) - a.toVal ≠ 0 := by rw [hsz_val, zero_sub]; exact neg_ne_zero.mpr ha_nz_val
    have hbv_round : (bv : Fp) = ○(s.toVal (R := R) - a.toVal) :=
      hbv.symm.trans (fpSubFinite_correct (R := R) s a hsa_ne)
    have ha_idem : ○(a.toVal (R := R)) = Fp.finite a :=
      RModeIdem.round_idempotent (R := R) a (Or.inr ha_nz)
    have hbv_neg_a : (bv : Fp) = Fp.finite (-a) := by
      rw [hbv_round, hsz_val, zero_sub, RModeConj.round_neg _ ha_nz_val,
          ha_idem, Fp.neg_finite]
    have hbv_val : bv.toVal (R := R) = -a.toVal := by
      rw [toVal_of_fp_eq (R := R) bv (-a) hbv_neg_a, FiniteFp.toVal_neg_eq_neg]
    -- av: s - bv = round(0 - (-a)) = round(a) = a
    have hsbv_ne : s.toVal (R := R) - bv.toVal ≠ 0 := by
      rw [hsz_val, zero_sub, hbv_val, neg_neg]; exact ha_nz_val
    have hav_round : (av : Fp) = ○(s.toVal (R := R) - bv.toVal) :=
      hav.symm.trans (fpSubFinite_correct (R := R) s bv hsbv_ne)
    have hav_eq_a : (av : Fp) = Fp.finite a := by
      rw [hav_round, hsz_val, zero_sub, hbv_val, neg_neg, ha_idem]
    have hav_val : av.toVal (R := R) = a.toVal := toVal_of_fp_eq (R := R) av a hav_eq_a
    -- ar = round(a - a) = 0
    obtain ⟨far, hfar_eq, hfar_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a av (by rw [hav_val])
    have har_val : ar.toVal (R := R) = 0 :=
      (toVal_of_fp_eq (R := R) ar far (har.symm.trans hfar_eq)).trans hfar_val
    -- br = round(b - bv) = round(b + a) = round(0) → signed zero
    have hbbv : b.toVal (R := R) - bv.toVal = 0 := by rw [hbv_val]; linarith
    obtain ⟨fbr, hfbr_eq, hfbr_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv (by linarith)
    have hbr_val : br.toVal (R := R) = 0 :=
      (toVal_of_fp_eq (R := R) br fbr (hbr.symm.trans hfbr_eq)).trans hfbr_val
    -- t = round(ar + br) = round(0 + 0) → signed zero
    have harb0 : ar.toVal (R := R) + br.toVal = 0 := by rw [har_val, hbr_val, add_zero]
    obtain ⟨ft, hft_eq, hft_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) ar br harb0
    have ht_val : t.toVal (R := R) = 0 :=
      (toVal_of_fp_eq (R := R) t ft (ht.symm.trans hft_eq)).trans hft_val
    rw [ht_val]; linarith
  · -- Nonzero sum: use weak splitting + post-processing
    -- Sterbenz shortcut: both positive, a ≥ b gives strong splitting
    -- All other cases: weak splitting via RModeSplit
    by_cases hSterbenz : a.s = false ∧ b.s = false ∧ (b.toVal (R := R)) ≤ a.toVal
    · obtain ⟨ha, hb, hab⟩ := hSterbenz
      exact twoSum_6op_pos (R := R) a b ha hb ha_nz hb_nz hab s hs bv hbv av hav br hbr ar har t ht
    · obtain ⟨hsplit, hav_exact⟩ := weak_splitting (R := R) a b ha_nz hsum_ne s hs bv hbv av hav
      exact twoSum_6op_of_weak_splitting (R := R) a b ha_nz hb_nz hsum_ne s hs
        bv av hbv hsplit hav_exact br hbr ar har t ht

end TwoSum6Op
