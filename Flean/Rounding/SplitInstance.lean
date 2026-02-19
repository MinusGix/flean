import Flean.Rounding.Rounding
import Flean.Rounding.ModeClass
import Flean.Rounding.PolicyInstances
import Flean.Rounding.GridInstance
import Flean.Rounding.SplitPositive
import Flean.ToVal
import Flean.Operations.AddErrorRepresentable
import Flean.Operations.Sub

/-! # RModeSplit — Instance for nearest rounding modes

Provides the `RModeSplit` instance by combining:
- Positive-case proofs from `SplitPositive.lean`
- Mixed-sign proofs via `dekker_mixed_sub_exact`
- Negation conjugacy to reduce all sign combinations -/

section SplitInstance

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **Dekker's theorem for mixed signs**: When a > 0, b < 0, and a + b > 0,
the subtraction s − a is exactly representable: bv = round(s − a) satisfies
bv.toVal = s.toVal − a.toVal. -/
private theorem dekker_mixed_sub_exact
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = true)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hab_pos : (0 : R) < (a.toVal : R) + b.toVal)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    bv.toVal (R := R) = s.toVal - a.toVal := by
  sorry

/-- Mixed-sign split_s_sub_bv: a positive, b negative. -/
private theorem split_s_sub_bv_mixed
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = true)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = s.toVal - bv.toVal := by
  by_cases hval : (s.toVal : R) - bv.toVal = 0
  · exact ⟨0, Or.inl rfl, by rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hval.symm⟩
  rcases lt_or_gt_of_ne hsum_ne with hab_neg | hab_pos
  · -- a + b < 0: |b| > |a| — TODO
    sorry
  · -- a + b > 0: Dekker applies
    have hbv_val := dekker_mixed_sub_exact (R := R) a b s ha hb ha_nz hb_nz hab_pos hsum_ne hs bv hbv
    exact ⟨a, Or.inl ha, by rw [hbv_val]; ring⟩

/-- Mixed-sign split_b_sub_bv: a positive, b negative. -/
private theorem split_b_sub_bv_mixed
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    [RModeGrid R]
    (a b s : FiniteFp)
    (ha : a.s = false) (hb : b.s = true)
    (ha_nz : 0 < a.m) (hb_nz : 0 < b.m)
    (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s)
    (bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ f : FiniteFp, (f.s = false ∨ 0 < f.m) ∧
      f.toVal (R := R) = b.toVal - bv.toVal := by
  by_cases hval : (b.toVal : R) - bv.toVal = 0
  · exact ⟨0, Or.inl rfl, by rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hval.symm⟩
  rcases lt_or_gt_of_ne hsum_ne with hab_neg | hab_pos
  · -- a + b < 0: |b| > |a| — TODO
    sorry
  · -- a + b > 0: Dekker gives bv = s - a exactly
    have hbv_val := dekker_mixed_sub_exact (R := R) a b s ha hb ha_nz hb_nz hab_pos hsum_ne hs bv hbv
    have ha_pos : (0 : R) < a.toVal := FiniteFp.toVal_pos a ha ha_nz
    have hb_neg : (b.toVal : R) < 0 := by
      have := FiniteFp.toVal_pos (-b) (by rw [FiniteFp.neg_def]; simp [hb])
        (by rw [FiniteFp.neg_def]; exact hb_nz) (R := R)
      rw [FiniteFp.toVal_neg_eq_neg] at this; linarith
    have hab_abs : |b.toVal (R := R)| ≤ |a.toVal| := by
      rw [abs_of_neg hb_neg, abs_of_pos ha_pos]; linarith
    have hs_fp : (a : Fp) + b = Fp.finite s := by
      have hcorr := fpAddFinite_correct (R := R) a b hsum_ne
      simp only [add_finite_eq_fpAddFinite] at hcorr
      exact hcorr.trans hs
    obtain ⟨t_fp, ht_valid, ht_val⟩ := add_error_representable_general (R := R)
      a b ha_nz hb_nz hab_abs hsum_ne s hs_fp
    exact ⟨t_fp, ht_valid, by rw [ht_val, hbv_val]; ring⟩

-- Helper: round of an FP value gives back the same value
private theorem round_fp_toVal [RMode R] [RModeExec] [RModeZero R] [RModeIdem R]
    (f g : FiniteFp) (h : ○(f.toVal (R := R)) = Fp.finite g) :
    g.toVal (R := R) = f.toVal := by
  by_cases hfm : f.m = 0
  · have hfv : f.toVal (R := R) = 0 := FiniteFp.toVal_isZero (show f.isZero from hfm)
    rw [hfv, RModeZero.round_zero] at h
    rw [show g = (0 : FiniteFp) from Fp.finite.inj h.symm, FiniteFp.toVal_isZero (R := R) rfl, hfv]
  · rw [RModeIdem.round_idempotent (R := R) f (Or.inr (by omega))] at h
    rw [show g = f from Fp.finite.inj h.symm]

-- Helper: if f represents -target_val ≠ 0, then -f represents target_val
private theorem neg_split_lift
    (f : FiniteFp) (hf_valid : f.s = false ∨ 0 < f.m)
    (target_val : R) (htarget_ne : target_val ≠ 0)
    (hf_val : f.toVal (R := R) = -target_val) :
    ∃ g : FiniteFp, (g.s = false ∨ 0 < g.m) ∧ g.toVal (R := R) = target_val := by
  have hf_nz : 0 < f.m := by
    rcases hf_valid with hfs | hfm
    · by_contra h; push_neg at h; have hm0 : f.m = 0 := by omega
      exact htarget_ne (neg_eq_zero.mp
        (by rw [← hf_val]; exact FiniteFp.toVal_isZero (show f.isZero from hm0)))
    · exact hfm
  exact ⟨-f, Or.inr (by rw [FiniteFp.neg_def]; exact hf_nz),
    by rw [FiniteFp.toVal_neg_eq_neg, hf_val, neg_neg]⟩

-- Helper: get a bv' for the negated problem with bv'.toVal = -bv.toVal
private theorem neg_bv_round
    [RMode R] [RModeExec] [RModeZero R] [RModeConj R]
    (s a bv : FiniteFp)
    (hbv : ○((s.toVal : R) - a.toVal) = Fp.finite bv) :
    ∃ bv' : FiniteFp,
      ○(((-s).toVal : R) - (-a).toVal) = Fp.finite bv' ∧
      bv'.toVal (R := R) = -bv.toVal := by
  rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg,
      show (-(s.toVal : R) - -a.toVal) = -(s.toVal - a.toVal) from by ring]
  by_cases hsa : (s.toVal : R) - a.toVal = 0
  · rw [hsa, neg_zero, RModeZero.round_zero]
    have hbv0 : bv = (0 : FiniteFp) := Fp.finite.inj
      ((by rw [hsa, RModeZero.round_zero] : ○((s.toVal : R) - a.toVal) = Fp.finite 0).symm.trans hbv).symm
    exact ⟨0, rfl, by subst hbv0; simp [FiniteFp.toVal_isZero (R := R) (show (0 : FiniteFp).isZero from rfl)]⟩
  · rw [RModeConj.round_neg _ hsa, hbv, Fp.neg_finite]
    exact ⟨-bv, rfl, FiniteFp.toVal_neg_eq_neg (R := R) bv⟩

-- Negation conjugacy helper for instance dispatch
private theorem negate_sum_round [RMode R] [RModeExec] [RModeConj R]
    (a b s : FiniteFp) (hsum_ne : (a.toVal : R) + b.toVal ≠ 0)
    (hs : ○((a.toVal : R) + b.toVal) = Fp.finite s) :
    ○(((-a).toVal : R) + (-b).toVal) = Fp.finite (-s) := by
  rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg,
      show (-(a.toVal : R) + -b.toVal) = -(a.toVal + b.toVal) from by ring,
      RModeConj.round_neg _ hsum_ne, hs, Fp.neg_finite]

-- Negation lift for split_s_sub_bv result (f'.toVal = -(target) → negate)
private theorem negate_split_s [RMode R]
    (s bv : FiniteFp) (f' : FiniteFp) (hf'_valid : f'.s = false ∨ 0 < f'.m)
    (hbv'_val : R) (hf'_val : f'.toVal (R := R) = (-s).toVal - hbv'_val) :
    f'.toVal (R := R) = -(s.toVal - (-hbv'_val)) := by
  rw [hf'_val, FiniteFp.toVal_neg_eq_neg]; ring

instance nearest_RModeSplit [RMode R] [RModeExec] [RoundIntSigMSound R]
    [RModeNearest R] [RModeConj R] : RModeSplit R where
  split_s_sub_bv a b s hs bv hbv := by
    by_cases ha_nz : 0 < a.m
    · by_cases hb_nz : 0 < b.m
      · by_cases hsum_ne : (a.toVal : R) + b.toVal ≠ 0
        · -- Nonzero sum: sign case split
          -- Note: Bool.eq_false_or_eq_true gives (= true) first, then (= false)
          by_cases ha : a.s = false
          · by_cases hb : b.s = false
            · -- Both positive
              exact split_s_sub_bv_pos a b s ha hb ha_nz hb_nz hsum_ne hs bv hbv
            · -- a positive, b negative
              have hb' : b.s = true := eq_true_of_ne_false hb
              exact split_s_sub_bv_mixed a b s ha hb' ha_nz hb_nz hsum_ne hs bv hbv
          · by_cases hb : b.s = false
            · -- a negative, b positive: negate both → (pos, neg) case
              have ha' : a.s = true := eq_true_of_ne_false ha
              have hna : (-a).s = false := by rw [FiniteFp.neg_def]; simp [ha']
              have hnb : (-b).s = true := by rw [FiniteFp.neg_def]; simp [hb]
              have hna_nz : 0 < (-a).m := by rw [FiniteFp.neg_def]; exact ha_nz
              have hnb_nz : 0 < (-b).m := by rw [FiniteFp.neg_def]; exact hb_nz
              have hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
                rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
                intro h; exact hsum_ne (by linarith)
              have hns := negate_sum_round (R := R) a b s hsum_ne hs
              obtain ⟨bv', hbv', hbv'_val⟩ := neg_bv_round (R := R) s a bv hbv
              obtain ⟨f', hf'_valid, hf'_val⟩ :=
                split_s_sub_bv_mixed (-a) (-b) (-s) hna hnb hna_nz hnb_nz hnsum_ne hns bv' hbv'
              have hf'_neg : f'.toVal (R := R) = -(s.toVal - bv.toVal) := by
                rw [hf'_val, FiniteFp.toVal_neg_eq_neg (R := R) s, hbv'_val]; ring
              by_cases hsbv : (s.toVal : R) - bv.toVal = 0
              · exact ⟨0, Or.inl rfl, by
                  rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hsbv.symm⟩
              · exact neg_split_lift (R := R) f' hf'_valid _ hsbv hf'_neg
            · -- Both negative: negate to positive case
              have ha' : a.s = true := eq_true_of_ne_false ha
              have hb' : b.s = true := eq_true_of_ne_false hb
              have hna : (-a).s = false := by rw [FiniteFp.neg_def]; simp [ha']
              have hnb : (-b).s = false := by rw [FiniteFp.neg_def]; simp [hb']
              have hna_nz : 0 < (-a).m := by rw [FiniteFp.neg_def]; exact ha_nz
              have hnb_nz : 0 < (-b).m := by rw [FiniteFp.neg_def]; exact hb_nz
              have hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
                rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
                intro h; exact hsum_ne (by linarith)
              have hns := negate_sum_round (R := R) a b s hsum_ne hs
              obtain ⟨bv', hbv', hbv'_val⟩ := neg_bv_round (R := R) s a bv hbv
              obtain ⟨f', hf'_valid, hf'_val⟩ :=
                split_s_sub_bv_pos (-a) (-b) (-s) hna hnb hna_nz hnb_nz hnsum_ne hns bv' hbv'
              have hf'_neg : f'.toVal (R := R) = -(s.toVal - bv.toVal) := by
                rw [hf'_val, FiniteFp.toVal_neg_eq_neg (R := R) s, hbv'_val]; ring
              by_cases hsbv : (s.toVal : R) - bv.toVal = 0
              · exact ⟨0, Or.inl rfl, by
                  rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hsbv.symm⟩
              · exact neg_split_lift (R := R) f' hf'_valid _ hsbv hf'_neg
        · -- Zero sum
          push_neg at hsum_ne
          have hs_val : s.toVal (R := R) = 0 := by
            have := round_fp_toVal (R := R) (0 : FiniteFp) s
              (by rw [FiniteFp.toVal_isZero (R := R) rfl]; rwa [hsum_ne] at hs)
            rw [this, FiniteFp.toVal_isZero (R := R) rfl]
          have ha_ne : (a.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos (R := R) a ha_nz
          have hbv_val : bv.toVal (R := R) = -a.toVal := by
            rw [hs_val, zero_sub] at hbv
            rw [RModeConj.round_neg _ ha_ne, RModeIdem.round_idempotent (R := R) a (Or.inr ha_nz),
                Fp.neg_finite] at hbv
            rw [show bv = -a from Fp.finite.inj hbv.symm, FiniteFp.toVal_neg_eq_neg]
          exact ⟨a, Or.inr ha_nz, by rw [hs_val, hbv_val]; ring⟩
      · -- b.m = 0
        have hb0 : b.toVal (R := R) = 0 :=
          FiniteFp.toVal_isZero (show b.isZero from by simp [FiniteFp.isZero]; omega)
        have hs_val : s.toVal (R := R) = a.toVal := by
          rw [hb0, add_zero] at hs
          exact round_fp_toVal (R := R) a s hs
        have hbv_val : bv.toVal (R := R) = 0 := by
          rw [hs_val, sub_self] at hbv
          rw [RModeZero.round_zero] at hbv
          rw [show bv = (0 : FiniteFp) from Fp.finite.inj hbv.symm,
              FiniteFp.toVal_isZero (R := R) rfl]
        exact ⟨a, Or.inr ha_nz, by rw [hs_val, hbv_val]; ring⟩
    · -- a.m = 0
      have ha0 : a.toVal (R := R) = 0 :=
        FiniteFp.toVal_isZero (show a.isZero from by simp [FiniteFp.isZero]; omega)
      have hs_val : s.toVal (R := R) = b.toVal := by
        rw [ha0, zero_add] at hs; exact round_fp_toVal (R := R) b s hs
      have hbv_val : bv.toVal (R := R) = s.toVal := by
        rw [ha0, sub_zero] at hbv; exact round_fp_toVal (R := R) s bv hbv
      exact ⟨0, Or.inl rfl, by
        rw [FiniteFp.toVal_isZero (R := R) rfl, hbv_val]; ring⟩
  split_b_sub_bv a b s hs bv hbv := by
    by_cases ha_nz : 0 < a.m
    · by_cases hb_nz : 0 < b.m
      · by_cases hsum_ne : (a.toVal : R) + b.toVal ≠ 0
        · by_cases ha : a.s = false
          · by_cases hb : b.s = false
            · exact split_b_sub_bv_pos a b s ha hb ha_nz hb_nz hsum_ne hs bv hbv
            · have hb' : b.s = true := eq_true_of_ne_false hb
              exact split_b_sub_bv_mixed a b s ha hb' ha_nz hb_nz hsum_ne hs bv hbv
          · by_cases hb : b.s = false
            · -- a negative, b positive: negate both
              have ha' : a.s = true := eq_true_of_ne_false ha
              have hna : (-a).s = false := by rw [FiniteFp.neg_def]; simp [ha']
              have hnb : (-b).s = true := by rw [FiniteFp.neg_def]; simp [hb]
              have hna_nz : 0 < (-a).m := by rw [FiniteFp.neg_def]; exact ha_nz
              have hnb_nz : 0 < (-b).m := by rw [FiniteFp.neg_def]; exact hb_nz
              have hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
                rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
                intro h; exact hsum_ne (by linarith)
              have hns := negate_sum_round (R := R) a b s hsum_ne hs
              obtain ⟨bv', hbv', hbv'_val⟩ := neg_bv_round (R := R) s a bv hbv
              obtain ⟨f', hf'_valid, hf'_val⟩ :=
                split_b_sub_bv_mixed (-a) (-b) (-s) hna hnb hna_nz hnb_nz hnsum_ne hns bv' hbv'
              have hf'_neg : f'.toVal (R := R) = -(b.toVal - bv.toVal) := by
                rw [hf'_val, FiniteFp.toVal_neg_eq_neg (R := R) b, hbv'_val]; ring
              by_cases hbbv : (b.toVal : R) - bv.toVal = 0
              · exact ⟨0, Or.inl rfl, by
                  rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hbbv.symm⟩
              · exact neg_split_lift (R := R) f' hf'_valid _ hbbv hf'_neg
            · -- Both negative
              have ha' : a.s = true := eq_true_of_ne_false ha
              have hb' : b.s = true := eq_true_of_ne_false hb
              have hna : (-a).s = false := by rw [FiniteFp.neg_def]; simp [ha']
              have hnb : (-b).s = false := by rw [FiniteFp.neg_def]; simp [hb']
              have hna_nz : 0 < (-a).m := by rw [FiniteFp.neg_def]; exact ha_nz
              have hnb_nz : 0 < (-b).m := by rw [FiniteFp.neg_def]; exact hb_nz
              have hnsum_ne : ((-a).toVal : R) + (-b).toVal ≠ 0 := by
                rw [FiniteFp.toVal_neg_eq_neg, FiniteFp.toVal_neg_eq_neg]
                intro h; exact hsum_ne (by linarith)
              have hns := negate_sum_round (R := R) a b s hsum_ne hs
              obtain ⟨bv', hbv', hbv'_val⟩ := neg_bv_round (R := R) s a bv hbv
              obtain ⟨f', hf'_valid, hf'_val⟩ :=
                split_b_sub_bv_pos (-a) (-b) (-s) hna hnb hna_nz hnb_nz hnsum_ne hns bv' hbv'
              have hf'_neg : f'.toVal (R := R) = -(b.toVal - bv.toVal) := by
                rw [hf'_val, FiniteFp.toVal_neg_eq_neg (R := R) b, hbv'_val]; ring
              by_cases hbbv : (b.toVal : R) - bv.toVal = 0
              · exact ⟨0, Or.inl rfl, by
                  rw [FiniteFp.toVal_isZero (R := R) rfl]; exact hbbv.symm⟩
              · exact neg_split_lift (R := R) f' hf'_valid _ hbbv hf'_neg
        · -- Zero sum
          push_neg at hsum_ne
          have hs_val : s.toVal (R := R) = 0 := by
            have := round_fp_toVal (R := R) (0 : FiniteFp) s
              (by rw [FiniteFp.toVal_isZero (R := R) rfl]; rwa [hsum_ne] at hs)
            rw [this, FiniteFp.toVal_isZero (R := R) rfl]
          have ha_ne : (a.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos (R := R) a ha_nz
          have hbv_val : bv.toVal (R := R) = -a.toVal := by
            rw [hs_val, zero_sub] at hbv
            rw [RModeConj.round_neg _ ha_ne, RModeIdem.round_idempotent (R := R) a (Or.inr ha_nz),
                Fp.neg_finite] at hbv
            rw [show bv = -a from Fp.finite.inj hbv.symm, FiniteFp.toVal_neg_eq_neg]
          exact ⟨0, Or.inl rfl, by
            rw [FiniteFp.toVal_isZero (R := R) rfl, hbv_val]; linarith⟩
      · -- b.m = 0
        have hb0 : b.toVal (R := R) = 0 :=
          FiniteFp.toVal_isZero (show b.isZero from by simp [FiniteFp.isZero]; omega)
        have hs_val : s.toVal (R := R) = a.toVal := by
          rw [hb0, add_zero] at hs; exact round_fp_toVal (R := R) a s hs
        have hbv_val : bv.toVal (R := R) = 0 := by
          rw [hs_val, sub_self] at hbv; rw [RModeZero.round_zero] at hbv
          rw [show bv = (0 : FiniteFp) from Fp.finite.inj hbv.symm,
              FiniteFp.toVal_isZero (R := R) rfl]
        exact ⟨0, Or.inl rfl, by
          rw [FiniteFp.toVal_isZero (R := R) rfl, hb0, hbv_val]; ring⟩
    · -- a.m = 0
      have ha0 : a.toVal (R := R) = 0 :=
        FiniteFp.toVal_isZero (show a.isZero from by simp [FiniteFp.isZero]; omega)
      have hs_val : s.toVal (R := R) = b.toVal := by
        rw [ha0, zero_add] at hs; exact round_fp_toVal (R := R) b s hs
      have hbv_val : bv.toVal (R := R) = s.toVal := by
        rw [ha0, sub_zero] at hbv; exact round_fp_toVal (R := R) s bv hbv
      exact ⟨0, Or.inl rfl, by
        rw [FiniteFp.toVal_isZero (R := R) rfl, hbv_val, hs_val]; ring⟩

end SplitInstance
