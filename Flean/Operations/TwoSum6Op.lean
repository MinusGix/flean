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
/-- If rounding of an FP value is finite, it preserves the exact value. -/
private theorem round_fp_toVal
    [RMode R] [RModeExec] [RModeZero R] [RModeIdem R]
    (f g : FiniteFp) (h : ○(f.toVal (R := R)) = Fp.finite g) :
    g.toVal (R := R) = f.toVal := by
  by_cases hfm : f.m = 0
  · have hfv : f.toVal (R := R) = 0 :=
      FiniteFp.toVal_isZero (show f.isZero from by
        simp [FiniteFp.isZero, hfm])
    rw [hfv, RModeZero.round_zero] at h
    rw [show g = (0 : FiniteFp) from Fp.finite.inj h.symm,
        FiniteFp.toVal_isZero (R := R) (show (0 : FiniteFp).isZero from rfl), hfv]
  · have hfm_pos : 0 < f.m := by
      exact Nat.pos_of_ne_zero hfm
    rw [RModeIdem.round_idempotent (R := R) f (Or.inr hfm_pos)] at h
    rw [show g = f from Fp.finite.inj h.symm]

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

private theorem weak_splitting_core
    (s bv : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs_sub_rep : ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = s.toVal - bv.toVal)
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
    obtain ⟨rep, hrep_valid, hrep_val⟩ := hs_sub_rep
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
private theorem twoSum_6op_of_weak_splitting_core (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv av : FiniteFp)
    (hbv : s - a = (bv : Fp))
    (hsplit : av.toVal (R := R) + bv.toVal = s.toVal)
    (hav_exact : av.toVal (R := R) = s.toVal - bv.toVal)
    (hbbv_rep : ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = b.toVal - bv.toVal)
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
  -- Step 2: b - bv is exact (from representability witness)
  have hbr_val : br.toVal (R := R) = b.toVal - bv.toVal := by
    by_cases hbbv : b.toVal (R := R) - bv.toVal = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv (by linarith)
      exact (toVal_of_fp_eq (R := R) br f (hbr.symm.trans hf_eq)).trans (hf_val.trans hbbv.symm)
    · obtain ⟨rep, hrep_valid, hrep_val⟩ := hbbv_rep
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

private theorem b_sub_bv_representable_of_bv_exact (a b s bv : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (hs : a + b = s)
    (hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal) :
    ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = b.toVal - bv.toVal := by
  obtain ⟨err, herr_valid, herr_eq⟩ := error_representable (R := R)
    a b ha_nz hb_nz hsum_ne s hs
  refine ⟨err, herr_valid, ?_⟩
  rw [herr_eq, hbv_exact]
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] in
private theorem s_sub_bv_representable_of_bv_exact (a s bv : FiniteFp)
    (ha_nz : 0 < a.m)
    (hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal) :
    ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = s.toVal - bv.toVal := by
  exact ⟨a, Or.inr ha_nz, by rw [hbv_exact]; ring⟩

/-! ## Nonzero-sum variant with explicit split witnesses -/

/-- 6-op correctness for nonzero exact sum, assuming explicit split witnesses.

Callers provide the two representability witnesses directly (`s-bv` and `b-bv`). -/
theorem twoSum_6op_nonzero_sum_of_witnesses (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hs_sub_rep : ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = s.toVal - bv.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (hbbv_rep : ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = b.toVal - bv.toVal)
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  obtain ⟨hsplit, hav_exact⟩ := weak_splitting_core (R := R) s bv hs_sub_rep av hav
  exact twoSum_6op_of_weak_splitting_core (R := R) a b ha_nz hb_nz hsum_ne s hs
    bv av hbv hsplit hav_exact hbbv_rep br hbr ar har t ht

/-- Nonzero-sum 6-op correctness from `s-bv` witness plus exact `bv = s-a`.

This discharges the `b-bv` witness automatically via
`b_sub_bv_representable_of_bv_exact`. -/
theorem twoSum_6op_nonzero_sum_of_s_witness_and_bv_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal)
    (hs_sub_rep : ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
      rep.toVal (R := R) = s.toVal - bv.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have hbbv_rep := b_sub_bv_representable_of_bv_exact (R := R)
    a b s bv ha_nz hb_nz hsum_ne hs hbv_exact
  exact twoSum_6op_nonzero_sum_of_witnesses (R := R)
    a b ha_nz hb_nz hsum_ne s hs bv hbv hs_sub_rep av hav hbbv_rep br hbr ar har t ht

/-- Nonzero-sum 6-op correctness from exact `bv = s-a`.

This discharges both split witnesses (`s-bv`, `b-bv`) automatically. -/
theorem twoSum_6op_nonzero_sum_of_bv_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hbv_exact : bv.toVal (R := R) = s.toVal - a.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have hs_sub_rep := s_sub_bv_representable_of_bv_exact (R := R) a s bv ha_nz hbv_exact
  exact twoSum_6op_nonzero_sum_of_s_witness_and_bv_exact (R := R)
    a b ha_nz hb_nz hsum_ne s hs bv hbv hbv_exact hs_sub_rep av hav br hbr ar har t ht

private theorem twoSum_6op_zero_sum (a b : FiniteFp)
    (ha_nz : 0 < a.m) (_hb_nz : 0 < b.m)
    (hsum_zero : (a.toVal : R) + b.toVal = 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have ha_nz_val : (a.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos a ha_nz
  obtain ⟨sz, hsz_eq, hsz_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) a b hsum_zero
  simp only [add_finite_eq_fpAddFinite] at hs hsz_eq
  have hs_eq : s = sz := Fp.finite.inj (hs.symm.trans hsz_eq)
  subst hs_eq; rw [hsz_val, zero_add]
  -- bv: s - a = round(0 - a) = round(-a) = -round(a) = -a
  have hsa_ne : s.toVal (R := R) - a.toVal ≠ 0 := by
    rw [hsz_val, zero_sub]
    exact neg_ne_zero.mpr ha_nz_val
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
    rw [hsz_val, zero_sub, hbv_val, neg_neg]
    exact ha_nz_val
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
  rw [ht_val]
  linarith

private theorem twoSum_6op_a_zero (a b : FiniteFp)
    (ha0 : a.m = 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have ha_val0 : a.toVal (R := R) = 0 := FiniteFp.toVal_isZero (show a.isZero from ha0)
  have hs_val : s.toVal (R := R) = b.toVal := by
    by_cases hb_val0 : b.toVal (R := R) = 0
    · have hsum0 : (a.toVal : R) + b.toVal = 0 := by rw [ha_val0, hb_val0, zero_add]
      obtain ⟨f, hf_eq, hf_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) a b hsum0
      have hs0 : s.toVal (R := R) = 0 :=
        (toVal_of_fp_eq (R := R) s f (hs.symm.trans hf_eq)).trans hf_val
      rw [hs0, hb_val0]
    · have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by simpa [ha_val0, zero_add] using hb_val0
      have hs_round : (s : Fp) = ○((a.toVal : R) + b.toVal) :=
        hs.symm.trans (fpAddFinite_correct (R := R) a b hsum_ne)
      have hs_round_b : ○(b.toVal (R := R)) = Fp.finite s := by
        simpa [ha_val0, zero_add] using hs_round.symm
      exact round_fp_toVal (R := R) b s hs_round_b
  have hbv_val : bv.toVal (R := R) = s.toVal := by
    by_cases hs0 : s.toVal (R := R) = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a
        (by linarith [hs0, ha_val0])
      have hbv0 : bv.toVal (R := R) = 0 :=
        (toVal_of_fp_eq (R := R) bv f (hbv.symm.trans hf_eq)).trans hf_val
      rw [hs0, hbv0]
    · have hsa_ne : s.toVal (R := R) - a.toVal ≠ 0 := by simpa [ha_val0, sub_zero] using hs0
      have hbv_round : (bv : Fp) = ○((s.toVal : R) - a.toVal) :=
        hbv.symm.trans (fpSubFinite_correct (R := R) s a hsa_ne)
      have hbv_round_s : ○(s.toVal (R := R)) = Fp.finite bv := by
        simpa [ha_val0, sub_zero] using hbv_round.symm
      exact round_fp_toVal (R := R) s bv hbv_round_s
  obtain ⟨fav, hfav_eq, hfav_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s bv (by linarith [hbv_val])
  have hav_val0 : av.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) av fav (hav.symm.trans hfav_eq)).trans hfav_val
  obtain ⟨fbr, hfbr_eq, hfbr_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv (by linarith [hs_val, hbv_val])
  have hbr_val0 : br.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) br fbr (hbr.symm.trans hfbr_eq)).trans hfbr_val
  obtain ⟨far, hfar_eq, hfar_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a av (by rw [ha_val0, hav_val0])
  have har_val0 : ar.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) ar far (har.symm.trans hfar_eq)).trans hfar_val
  obtain ⟨ft, hft_eq, hft_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) ar br
    (by rw [har_val0, hbr_val0, add_zero])
  have ht_val0 : t.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) t ft (ht.symm.trans hft_eq)).trans hft_val
  rw [ht_val0, ha_val0, zero_add, add_zero]
  exact hs_val

private theorem twoSum_6op_b_zero (a b : FiniteFp)
    (hb0 : b.m = 0)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  have hb_val0 : b.toVal (R := R) = 0 := FiniteFp.toVal_isZero (show b.isZero from hb0)
  have hs_val : s.toVal (R := R) = a.toVal := by
    by_cases ha_val0 : a.toVal (R := R) = 0
    · have hsum0 : (a.toVal : R) + b.toVal = 0 := by rw [ha_val0, hb_val0, add_zero]
      obtain ⟨f, hf_eq, hf_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) a b hsum0
      have hs0 : s.toVal (R := R) = 0 :=
        (toVal_of_fp_eq (R := R) s f (hs.symm.trans hf_eq)).trans hf_val
      rw [hs0, ha_val0]
    · have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := by simpa [hb_val0, add_zero] using ha_val0
      have hs_round : (s : Fp) = ○((a.toVal : R) + b.toVal) :=
        hs.symm.trans (fpAddFinite_correct (R := R) a b hsum_ne)
      have hs_round_a : ○(a.toVal (R := R)) = Fp.finite s := by
        simpa [hb_val0, add_zero] using hs_round.symm
      exact round_fp_toVal (R := R) a s hs_round_a
  obtain ⟨fbv, hfbv_eq, hfbv_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s a (by linarith [hs_val])
  have hbv_val0 : bv.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) bv fbv (hbv.symm.trans hfbv_eq)).trans hfbv_val
  have hav_val : av.toVal (R := R) = s.toVal := by
    by_cases hs0 : s.toVal (R := R) = 0
    · obtain ⟨f, hf_eq, hf_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) s bv
        (by linarith [hs0, hbv_val0])
      have hav0 : av.toVal (R := R) = 0 :=
        (toVal_of_fp_eq (R := R) av f (hav.symm.trans hf_eq)).trans hf_val
      rw [hs0, hav0]
    · have hsbv_ne : s.toVal (R := R) - bv.toVal ≠ 0 := by simpa [hbv_val0, sub_zero] using hs0
      have hav_round : (av : Fp) = ○((s.toVal : R) - bv.toVal) :=
        hav.symm.trans (fpSubFinite_correct (R := R) s bv hsbv_ne)
      have hav_round_s : ○(s.toVal (R := R)) = Fp.finite av := by
        simpa [hbv_val0, sub_zero] using hav_round.symm
      exact round_fp_toVal (R := R) s av hav_round_s
  obtain ⟨fbr, hfbr_eq, hfbr_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) b bv
    (by linarith [hb_val0, hbv_val0])
  have hbr_val0 : br.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) br fbr (hbr.symm.trans hfbr_eq)).trans hfbr_val
  obtain ⟨far, hfar_eq, hfar_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a av (by linarith [hs_val, hav_val])
  have har_val0 : ar.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) ar far (har.symm.trans hfar_eq)).trans hfar_val
  obtain ⟨ft, hft_eq, hft_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) ar br
    (by rw [har_val0, hbr_val0, add_zero])
  have ht_val0 : t.toVal (R := R) = 0 :=
    (toVal_of_fp_eq (R := R) t ft (ht.symm.trans hft_eq)).trans hft_val
  rw [ht_val0, hb_val0, add_zero, add_zero]
  exact hs_val

/-- 6-op correctness from explicit nonzero-branch split witnesses. -/
theorem twoSum_6op_of_witnesses (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hs_sub_rep :
      ((a.toVal : R) + b.toVal ≠ 0) →
      ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
        rep.toVal (R := R) = s.toVal - bv.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (hbbv_rep :
      ((a.toVal : R) + b.toVal ≠ 0) →
      ∃ rep : FiniteFp, (rep.s = false ∨ 0 < rep.m) ∧
        rep.toVal (R := R) = b.toVal - bv.toVal)
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  by_cases hsum_zero : (a.toVal : R) + b.toVal = 0
  · exact twoSum_6op_zero_sum (R := R) a b ha_nz hb_nz hsum_zero
      s hs bv hbv av hav br hbr ar har t ht
  · have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := hsum_zero
    exact twoSum_6op_nonzero_sum_of_witnesses (R := R) a b ha_nz hb_nz hsum_ne
      s hs bv hbv (hs_sub_rep hsum_ne) av hav (hbbv_rep hsum_ne) br hbr ar har t ht

/-- 6-op correctness from exact `bv = s-a` on the nonzero-sum branch.

This is a practical top-level theorem without explicit split witnesses. -/
theorem twoSum_6op_of_bv_exact (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hbv_exact :
      ((a.toVal : R) + b.toVal ≠ 0) →
      bv.toVal (R := R) = s.toVal - a.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  by_cases hsum_zero : (a.toVal : R) + b.toVal = 0
  · exact twoSum_6op_zero_sum (R := R) a b ha_nz hb_nz hsum_zero
      s hs bv hbv av hav br hbr ar har t ht
  · have hsum_ne : (a.toVal : R) + b.toVal ≠ 0 := hsum_zero
    exact twoSum_6op_nonzero_sum_of_bv_exact (R := R)
      a b ha_nz hb_nz hsum_ne s hs bv hbv (hbv_exact hsum_ne)
      av hav br hbr ar har t ht

/-! ## Main theorem -/

/-- **6-op 2Sum correctness** for nonzero inputs, with exactness of
the first split subtraction on the nonzero-sum branch. -/
theorem twoSum_6op_nonzero (a b : FiniteFp)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hbv_exact :
      ((a.toVal : R) + b.toVal ≠ 0) →
      bv.toVal (R := R) = s.toVal - a.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  exact twoSum_6op_of_bv_exact (R := R) a b ha_nz hb_nz s hs bv hbv
    hbv_exact av hav br hbr ar har t ht

/-- **6-op 2Sum correctness** for arbitrary finite floats, with exactness of
the first split subtraction on the nonzero-sum branch. -/
theorem twoSum_6op (a b : FiniteFp)
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    (s : FiniteFp) (hs : a + b = s)
    (bv : FiniteFp) (hbv : s - a = (bv : Fp))
    (hbv_exact :
      ((a.toVal : R) + b.toVal ≠ 0) →
      bv.toVal (R := R) = s.toVal - a.toVal)
    (av : FiniteFp) (hav : s - bv = (av : Fp))
    (br : FiniteFp) (hbr : b - bv = (br : Fp))
    (ar : FiniteFp) (har : a - av = (ar : Fp))
    (t : FiniteFp) (ht : ar + br = (t : Fp)) :
    (s.toVal : R) + t.toVal = a.toVal + b.toVal := by
  by_cases ha_nz : 0 < a.m
  · by_cases hb_nz : 0 < b.m
    · exact twoSum_6op_nonzero (R := R) a b ha_nz hb_nz s hs bv hbv
        hbv_exact av hav br hbr ar har t ht
    · have hb0 : b.m = 0 := Nat.eq_zero_of_not_pos hb_nz
      exact twoSum_6op_b_zero (R := R) a b hb0 s hs bv hbv av hav br hbr ar har t ht
  · have ha0 : a.m = 0 := Nat.eq_zero_of_not_pos ha_nz
    exact twoSum_6op_a_zero (R := R) a b ha0 s hs bv hbv av hav br hbr ar har t ht

end TwoSum6Op
