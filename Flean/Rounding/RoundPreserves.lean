import Flean.Rounding.ModeClass
import Flean.Order
import Flean.Operations.KahanSum

/-!
# Meta-lemmas: rounding preserves semantic tags

Per `.claude/notes/tag-framework-phase1-design.md` §3.1. Collects the
"round preserves P" meta-lemmas used by tag-framework preservation
proofs. Each lemma takes a pre-existing `RMode` plus the specific
`RMode*` class(es) needed for its preservation law, and lifts a
property on the real pre-image to a property on the rounded float.

Downstream tag preservation theorems (e.g. `IsNonneg.fpAdd` in
`Flean/Tags/Nonneg.lean`) reduce to: get a rounding witness from
`Flean/Operations/FpFiniteRound.lean`, then apply the appropriate
meta-lemma here.

Currently populated:
- `round_preserves_nonneg` — via `RModeMono` + `RModeZero`.
- `round_preserves_abs_bound_normal` — via `RModeNearest` +
  `standard_error_additive`. For parametric `HasAbsBound c` tags in
  the normal-range regime (non-negative inputs only).
- `round_preserves_abs_error_normal` — sign-agnostic additive error
  bound `|f.toVal - x| ≤ η·|x|` for any `x` with
  `2^min_exp ≤ |x|`, via `RModeNearest` + `RModeConj`. Underpins the
  parametric interval-propagation lemmas in
  `Flean/Tags/BoundedRangePropagate.lean`.
- `round_preserves_abs_error_unified` — subnormal-tolerant
  sign-agnostic bound
  `|f.toVal - x| ≤ η·|x| + 2^(min_exp - prec)`
  holding unconditionally (handles `x = 0`, subnormal, and normal
  ranges).  Trades the `2^min_exp ≤ |x|` precondition for an additive
  `subnormalConst`-style tail.  Underpins
  `IsBoundedRange.fp{Add,Mul}_unified`.

Future additions (as tags demand):
- `round_preserves_pos` — `IsPos` is NOT generally round-preserved
  (tiny positives underflow to 0); a useful variant would add a
  lower-magnitude hypothesis that avoids the underflow zone.
- etc.
-/

section RoundPreserves

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `x ≥ 0` and rounding `x` yields a finite float `f`, then
`0 ≤ f.toVal`. The universal kernel underlying any "round preserves
non-negative" tag preservation.

Uses only `RModeMono` (order-preservation) and `RModeZero` (zero is
round-stable). All standard rounding modes in Flean satisfy both, so
this lemma composes with any of them. -/
theorem round_preserves_nonneg [RMode R] [RModeMono R] [RModeZero R]
    {x : R} (hx : 0 ≤ x) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    (0 : R) ≤ f.toVal := by
  have h_mono := RModeMono.round_mono (R := R) hx
  rw [RModeZero.round_zero (R := R), hf] at h_mono
  have hle : (0 : FiniteFp) ≤ f := (Fp.finite_le_finite_iff 0 f).mp h_mono
  have := FiniteFp.le_toVal_le R hle
  rwa [FiniteFp.toVal_zero] at this

/-- If `|x| ≤ c` with `x` in the (positive) normal range, then rounding
`x` yields a finite `f` with `|f.toVal| ≤ (1+η)·c`. The kernel for any
parametric `HasAbsBound c` tag preservation, in the normal-range regime.

Uses `KahanSum.standard_error_additive` (`|f - x| ≤ η·|x|` for normal-range
positive `x` under `RModeNearest`). A sign-agnostic / subnormal-tolerant
version is future work — see the module docstring. -/
theorem round_preserves_abs_bound_normal [FloorRing R] [RMode R] [RModeNearest R]
    {x c : R} (hxc : |x| ≤ c) (hx_normal : isNormalRange x)
    {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R)| ≤ (1 + η) * c := by
  have hx_pos := isNormalRange_pos x hx_normal
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have h_err := KahanSum.standard_error_additive x hx_normal f hf
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have h_step1 : |(f.toVal : R)| ≤ |f.toVal - x| + |x| := by
    have : |((f.toVal - x) + x : R)| ≤ |f.toVal - x| + |x| := abs_add_le _ _
    convert this using 2
    ring
  calc |(f.toVal : R)|
      ≤ |f.toVal - x| + |x| := h_step1
    _ ≤ η * |x| + |x| := by linarith
    _ = (1 + η) * |x| := by ring
    _ ≤ (1 + η) * c := mul_le_mul_of_nonneg_left hxc h1η_nn

/-- Sign-agnostic additive error bound: for any `x` with
`2^min_exp ≤ |x|` (so `x ≠ 0` and is no tinier than the smallest
normal), rounding `x` to a finite float `f` satisfies
`|f.toVal - x| ≤ η · |x|`.

The finiteness hypothesis `hf` forces `|x| < overflowThreshold <
2^(max_exp+1)`, so we don't need to take the upper normal-range bound
as a user hypothesis.

Proof dispatches on the sign of `x`: positive inputs use
`standard_error_additive` directly; negative inputs reduce to the
positive case via `RModeConj.round_neg`.

This is the interval-propagation companion of `round_preserves_abs_bound_normal`
(which fixes a single magnitude bound `c` and is non-negative-only).  -/
theorem round_preserves_abs_error_normal [FloorRing R]
    [RMode R] [RModeNearest R] [RModeConj R]
    {x : R} (hx_lb : (2 : R) ^ FloatFormat.min_exp ≤ |x|)
    {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R) - x| ≤ η * |x| := by
  have h_pos_min : (0 : R) < (2 : R) ^ (FloatFormat.min_exp : ℤ) := by linearize
  have hx_abs_pos : (0 : R) < |x| := lt_of_lt_of_le h_pos_min hx_lb
  have hx_ne : x ≠ 0 := fun h => by
    rw [h, abs_zero] at hx_abs_pos; exact lt_irrefl _ hx_abs_pos
  -- From finiteness of `round x`, derive `|x| < 2^(max_exp+1)`.
  have hx_lt_max : |x| < (2 : R) ^ (FloatFormat.max_exp + 1) := by
    by_contra h; push_neg at h
    have hx_lt_ot_imp : FloatFormat.overflowThreshold R ≤ |x| :=
      le_trans (le_of_lt FloatFormat.overflowThreshold_lt_zpow_max_exp_succ) h
    rcases lt_or_gt_of_ne hx_ne with hneg | hpos
    · have habs_neg : |x| = -x := abs_of_neg hneg
      rw [habs_neg] at hx_lt_ot_imp
      have := RModeNearest.overflow_pos_inf (-x) hx_lt_ot_imp
      have hconj := RModeConj.round_neg x hx_ne
      rw [hf, Fp.neg_finite] at hconj
      rw [hconj] at this; cases this
    · have habs_pos : |x| = x := abs_of_pos hpos
      rw [habs_pos] at hx_lt_ot_imp
      have := RModeNearest.overflow_pos_inf x hx_lt_ot_imp
      rw [this] at hf; cases hf
  rcases lt_or_gt_of_ne hx_ne with hneg | hpos
  · -- Negative input: reduce to positive via `RModeConj`.
    have hNR_neg : isNormalRange (-x) := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_neg hneg] at hx_lb
      · rwa [abs_of_neg hneg] at hx_lt_max
    have hconj : (RMode.round (-x) : Fp) = Fp.finite (-f) := by
      rw [RModeConj.round_neg x hx_ne, hf, Fp.neg_finite]
    have h := KahanSum.standard_error_additive (-x) hNR_neg (-f) hconj
    rw [FiniteFp.toVal_neg_eq_neg (R := R) f, abs_neg] at h
    have hrewrite : |(-(f.toVal : R)) - (-x)| = |(f.toVal : R) - x| := by
      rw [show (-(f.toVal : R)) - (-x) = -((f.toVal : R) - x) from by ring, abs_neg]
    rwa [hrewrite] at h
  · -- Positive input: direct application.
    have hNR : isNormalRange x := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_pos hpos] at hx_lb
      · rwa [abs_of_pos hpos] at hx_lt_max
    exact KahanSum.standard_error_additive x hNR f hf

/-! ## Subnormal-tolerant unified bound -/

/-- R-generic subnormal-tolerant ulp-half bound.  For any positive `v`,
`ulp v / 2 ≤ η·v + 2^(min_exp - prec)`.  Mirrors
`Softmax.ulp_half_le_unified` (ℝ-specific) but holds over any ordered
field with a `FloorRing`.  Case-splits on normal vs subnormal `v`. -/
private theorem ulp_half_le_unified_gen [FloorRing R] (v : R) (hv_pos : 0 < v) :
    Fp.ulp v / 2 ≤
      (η : R) * v + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  unfold Fp.ulp
  simp only [FloatFormat.hEps_def]
  set e : ℤ := max (Int.log 2 |v|) FloatFormat.min_exp with he_def
  have hv_abs : |v| = v := abs_of_pos hv_pos
  have hη_pos : (0 : R) < (2 : R) ^ (-(FloatFormat.prec : ℤ)) := by positivity
  have hsub_pos : (0 : R) < (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
    positivity
  have halgebra : (2 : R) ^ (e - FloatFormat.prec + 1) / 2 =
      (2 : R) ^ (e - FloatFormat.prec) := by
    rw [zpow_add_one₀ (by norm_num : (2 : R) ≠ 0)]; ring
  rw [halgebra]
  by_cases hnormal : (2 : R) ^ FloatFormat.min_exp ≤ v
  · -- Normal-range branch.
    have hlog_ge : FloatFormat.min_exp ≤ Int.log 2 |v| := by
      rw [hv_abs]
      exact (Int.zpow_le_iff_le_log (b := 2) (R := R)
        (by norm_num : (1 : ℕ) < 2) hv_pos).mp hnormal
    have he_eq : e = Int.log 2 |v| := by
      rw [he_def]; exact max_eq_left hlog_ge
    rw [he_eq]
    have hlog_le_v : (2 : R) ^ (Int.log 2 |v|) ≤ v := by
      have h := Int.zpow_log_le_self (R := R) (b := 2)
        (by norm_num : (1 : ℕ) < 2) hv_pos
      calc (2 : R) ^ (Int.log 2 |v|) = (2 : R) ^ (Int.log 2 v) := by rw [hv_abs]
        _ ≤ v := by exact_mod_cast h
    have h1 : (2 : R) ^ (Int.log 2 |v| - FloatFormat.prec) =
        (2 : R) ^ (Int.log 2 |v|) * (2 : R) ^ (-(FloatFormat.prec : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : R) ≠ 0)]; ring_nf
    rw [h1]
    calc (2 : R) ^ (Int.log 2 |v|) * (2 : R) ^ (-(FloatFormat.prec : ℤ))
        ≤ v * (2 : R) ^ (-(FloatFormat.prec : ℤ)) :=
          mul_le_mul_of_nonneg_right hlog_le_v (le_of_lt hη_pos)
      _ = (2 : R) ^ (-(FloatFormat.prec : ℤ)) * v := by ring
      _ ≤ (2 : R) ^ (-(FloatFormat.prec : ℤ)) * v +
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by linarith
  · -- Subnormal-range branch: 0 < v < 2^min_exp.
    push_neg at hnormal
    have hlog_lt : Int.log 2 |v| < FloatFormat.min_exp := by
      rw [hv_abs]
      by_contra h_ge
      push_neg at h_ge
      have : (2 : R) ^ FloatFormat.min_exp ≤ v := by
        have h1 : (2 : R) ^ (FloatFormat.min_exp : ℤ) ≤ (2 : R) ^ Int.log 2 v :=
          zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) h_ge
        have h2 : (2 : R) ^ Int.log 2 v ≤ v :=
          Int.zpow_log_le_self (R := R) (b := 2)
            (by norm_num : (1 : ℕ) < 2) hv_pos
        linarith
      linarith
    have he_eq : e = FloatFormat.min_exp := by
      rw [he_def]; exact max_eq_right (le_of_lt hlog_lt)
    rw [he_eq]
    linarith [mul_nonneg (le_of_lt hη_pos) (le_of_lt hv_pos)]

/-- Subnormal-tolerant sign-agnostic additive error bound:
`|f.toVal - x| ≤ η·|x| + 2^(min_exp - prec)` for *any* real `x` whose
rounded image is finite, via `RModeNearest` + `RModeConj` + `RModeZero`.

Drops the `2^min_exp ≤ |x|` hypothesis of
`round_preserves_abs_error_normal` in exchange for a `subnormalConst`
tail (`2^(min_exp - prec)`), which absorbs the absolute rounding error
in the subnormal range.  Handles `x = 0`, subnormal `x`, and normal `x`
uniformly.

The companion of `Softmax.ulp_half_le_unified`'s role in LogSumExp,
now at tag-framework meta-lemma level.  Underpins
`IsBoundedRange.fp{Add,Mul}_unified`. -/
theorem round_preserves_abs_error_unified [FloorRing R]
    [RMode R] [RModeNearest R] [RModeConj R] [RModeZero R]
    (x : R) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R) - x| ≤
      (η : R) * |x| +
        (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have hsub_nn : (0 : R) ≤ (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
    positivity
  by_cases hx_zero : x = 0
  · -- Zero-case: `f.toVal = 0` by `RModeZero`.
    subst hx_zero
    have hround0 : (RMode.round (0 : R) : Fp) = Fp.finite 0 := RModeZero.round_zero
    rw [hround0] at hf
    have hf_eq : f = (0 : FiniteFp) := (Fp.finite.inj hf).symm
    rw [hf_eq, FiniteFp.toVal_zero, sub_zero, abs_zero]
    linarith
  rcases lt_or_gt_of_ne hx_zero with hneg | hpos
  · -- Negative input: conjugate to positive.
    have hneg_pos : 0 < -x := by linarith
    have h_round_neg : (RMode.round (-x) : Fp) = Fp.finite (-f) := by
      rw [RModeConj.round_neg x hx_zero, hf, Fp.neg_finite]
    have h_err_neg : |(-x) - ((-f).toVal : R)| ≤ Fp.ulp (-x) / 2 :=
      RModeNearest_abs_error_le_ulp_half_pos (-x) hneg_pos (-f) h_round_neg
    have hulp_bound := ulp_half_le_unified_gen (R := R) (-x) hneg_pos
    have habs_x : |x| = -x := abs_of_neg hneg
    rw [FiniteFp.toVal_neg_eq_neg (R := R) f] at h_err_neg
    have hrewrite :
        |(-x) - (-(f.toVal : R))| = |(f.toVal : R) - x| := by
      rw [show (-x) - (-(f.toVal : R)) = (f.toVal : R) - x from by ring]
    rw [hrewrite] at h_err_neg
    rw [habs_x]
    linarith
  · -- Positive input: direct application.
    have h_err : |x - (f.toVal : R)| ≤ Fp.ulp x / 2 :=
      RModeNearest_abs_error_le_ulp_half_pos x hpos f hf
    have hulp_bound := ulp_half_le_unified_gen (R := R) x hpos
    have habs_x : |x| = x := abs_of_pos hpos
    have hsymm : |x - (f.toVal : R)| = |(f.toVal : R) - x| := abs_sub_comm _ _
    rw [hsymm] at h_err
    rw [habs_x]
    linarith

/-! ## Sign-agnostic magnitude bounds

Companions of `round_preserves_abs_bound_normal` (which requires
`isNormalRange x`, i.e. `x > 0`).  Built on top of the sign-agnostic
`round_preserves_abs_error_*` family.

Used as the kernel for `HasAbsBound` propagation through FP ops in
`Flean/Tags/AbsBoundPropagate.lean`. -/

/-- Sign-agnostic magnitude bound in the normal range.

Given `|x| ≤ c` and `2^min_exp ≤ |x|` (i.e. `x` is outside the
subnormal zone), rounding `x` to a finite float `f` yields
`|f.toVal| ≤ (1+η)·c`.

Drops the `isNormalRange x` (positive) hypothesis of
`round_preserves_abs_bound_normal` by using
`round_preserves_abs_error_normal` + triangle inequality instead.
Pays for this with the `RModeConj` typeclass. -/
theorem round_preserves_abs_bound_signed_normal [FloorRing R]
    [RMode R] [RModeNearest R] [RModeConj R]
    {x c : R} (hxc : |x| ≤ c)
    (hx_lb : (2 : R) ^ FloatFormat.min_exp ≤ |x|)
    {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R)| ≤ (1 + η) * c := by
  have h_err : |(f.toVal : R) - x| ≤ η * |x| :=
    round_preserves_abs_error_normal hx_lb hf
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have h_tri : |(f.toVal : R)| ≤ |(f.toVal : R) - x| + |x| := by
    have : |((f.toVal : R) - x) + x| ≤ |(f.toVal : R) - x| + |x| := abs_add_le _ _
    convert this using 2; ring
  calc |(f.toVal : R)|
      ≤ |(f.toVal : R) - x| + |x| := h_tri
    _ ≤ η * |x| + |x| := by linarith
    _ = (1 + η) * |x| := by ring
    _ ≤ (1 + η) * c := mul_le_mul_of_nonneg_left hxc h1η_nn

/-- Sign-agnostic subnormal-tolerant magnitude bound.

Given `|x| ≤ c`, rounding `x` to a finite float `f` yields
`|f.toVal| ≤ (1+η)·c + subnormalConst`, where
`subnormalConst = 2^(min_exp - prec)`.

Drops both the `isNormalRange x` hypothesis AND the magnitude lower
bound of `round_preserves_abs_bound_signed_normal`, in exchange for
the subnormal tail.  Uses `round_preserves_abs_error_unified`. -/
theorem round_preserves_abs_bound_unified [FloorRing R]
    [RMode R] [RModeNearest R] [RModeConj R] [RModeZero R]
    {x c : R} (hxc : |x| ≤ c) {f : FiniteFp}
    (hf : (RMode.round x : Fp) = Fp.finite f) :
    |(f.toVal : R)| ≤ (1 + η) * c +
      (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
  have h_err := round_preserves_abs_error_unified (R := R) x hf
  have hη_nn : (0 : R) ≤ η := by positivity
  have h1η_nn : (0 : R) ≤ 1 + η := by linarith
  have hsub_nn : (0 : R) ≤ (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) :=
    by positivity
  have h_tri : |(f.toVal : R)| ≤ |(f.toVal : R) - x| + |x| := by
    have : |((f.toVal : R) - x) + x| ≤ |(f.toVal : R) - x| + |x| := abs_add_le _ _
    convert this using 2; ring
  calc |(f.toVal : R)|
      ≤ |(f.toVal : R) - x| + |x| := h_tri
    _ ≤ (η * |x| +
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)) + |x| := by linarith
    _ = (1 + η) * |x| +
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring
    _ ≤ (1 + η) * c +
          (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by
          have := mul_le_mul_of_nonneg_left hxc h1η_nn
          linarith

end RoundPreserves
