import Flean.Operations.ModAddClockBinary32

/-! # End-to-end Binary32 modular addition

This file removes the ideal-sum oracle from `ModAddClockBinary32.lean`.  It constructs the Fourier
feature of `a+b` from the separately stored Binary32 features of `a` and `b`, then evaluates the
Binary32 readout with a subnormal-safe sequential FMA model.

The construction follows the clock identities frequency by frequency:

```text
cos(k(a+b)) = cos(ka)cos(kb) - sin(ka)sin(kb)
sin(k(a+b)) = sin(ka)cos(kb) + cos(ka)sin(kb).
```

Each coordinate uses one rounded product and one rounded FMA.  The readout folds 224 exact-product
FMA steps.  All rounding is Binary32 round-to-nearest, ties-to-even; no normal-range hypothesis is
imposed on intermediate cancellations.  The subnormal tail is included explicitly.
-/

set_option autoImplicit false

namespace Flean.ModAddClock.Binary32

open Real Finset BigOperators

private local instance binary32FormatE2E : FloatFormat := FloatFormat.Binary32.toFloatFormat
private local instance nearestEvenPolicyE2E : UseRoundingPolicy RoundNearestEvenPolicy := {}
private local instance prime113E2E : Fact (Nat.Prime 113) := ⟨by decide⟩

/-- Uniform error assigned to a feature coordinate recovered from separate inputs. -/
noncomputable def compositionError : ℝ := (1 : ℝ) / 100000

theorem compositionError_nonneg : 0 ≤ compositionError := by
  norm_num [compositionError]

private theorem tableError_le_micro : tableError ≤ (1 : ℝ) / 1000000 := by
  norm_num [tableError]

private theorem small_bound_le_largest (x : ℝ) (hx : |x| ≤ 1120) :
    |x| ≤ FiniteFp.largestFiniteFloat.toVal := by
  refine hx.trans ?_
  rw [FiniteFp.largestFiniteFloat_toVal]
  change (1120 : ℝ) ≤ 2 ^ (127 : ℤ) * (2 - 2 ^ (-23 : ℤ))
  norm_num

/-- Rounding any intermediate of magnitude at most nine contributes at most one micro-unit. -/
private theorem round_error_le_micro (x : ℝ) (hx : |x| ≤ 9) :
    |((round x).toVal : ℝ) - x| ≤ (1 : ℝ) / 1000000 := by
  have h := round_error_le_unified x (small_bound_le_largest x (hx.trans (by norm_num)))
  have hnum : (2 : ℝ) ^ (-24 : ℤ) * 9 + (2 : ℝ) ^ (-150 : ℤ) ≤
      (1 : ℝ) / 1000000 := by norm_num
  calc
    |((round x).toVal : ℝ) - x| ≤
        (2 : ℝ) ^ (-24 : ℤ) * |x| + (2 : ℝ) ^ (-150 : ℤ) := h
    _ ≤ (2 : ℝ) ^ (-24 : ℤ) * 9 + (2 : ℝ) ^ (-150 : ℤ) := by gcongr
    _ ≤ (1 : ℝ) / 1000000 := hnum

/-- A stored table entry has magnitude at most two. -/
private theorem entry_abs_le_two {p n : ℕ} (B : FrequencyBank p n) (x : ZMod p)
    (j : Fin (n + n)) : |((entry B x j).toVal : ℝ)| ≤ 2 := by
  have hclose := entry_close B x j
  have hdiff := abs_sub_abs_le_abs_sub ((entry B x j).toVal : ℝ) (B.feature x j)
  have hideal := B.abs_feature_le_one x j
  linarith [tableError_le_micro]

/-- Product perturbation from two rounded table entries, before rounding the operation itself. -/
private theorem stored_mul_close
    {x y x₀ y₀ : ℝ}
    (hy : |y| ≤ 2) (hx₀ : |x₀| ≤ 1)
    (hxc : |x - x₀| ≤ tableError) (hyc : |y - y₀| ≤ tableError) :
    |x * y - x₀ * y₀| ≤ (3 : ℝ) / 1000000 := by
  calc
    |x * y - x₀ * y₀| = |(x - x₀) * y + x₀ * (y - y₀)| := by ring_nf
    _ ≤ |(x - x₀) * y| + |x₀ * (y - y₀)| := abs_add_le _ _
    _ = |x - x₀| * |y| + |x₀| * |y - y₀| := by rw [abs_mul, abs_mul]
    _ ≤ tableError * 2 + 1 * tableError := by
      gcongr
      exact tableError_nonneg
    _ ≤ (3 : ℝ) / 1000000 := by nlinarith [tableError_le_micro]

/-- One rounded multiplication of finite Binary32 operands. -/
noncomputable def roundedProduct (x y : FiniteFp) : FiniteFp :=
  round ((x.toVal : ℝ) * y.toVal)

/-- One rounded fused multiply-add of finite Binary32 operands. -/
noncomputable def roundedFMA (x y z : FiniteFp) : FiniteFp :=
  round ((x.toVal : ℝ) * y.toVal + z.toVal)

/-- The generic two-product building block used for both cosine and sine composition. -/
noncomputable def roundedBilinear (x y z w : FiniteFp) : FiniteFp :=
  roundedFMA x y (roundedProduct z w)

/-- A rounded product of table-scale operands is within four micro-units of the corresponding exact
real product. -/
private theorem roundedProduct_close
    {x y : FiniteFp} {x₀ y₀ : ℝ}
    (hx : |(x.toVal : ℝ)| ≤ 2) (hy : |(y.toVal : ℝ)| ≤ 2)
    (hx₀ : |x₀| ≤ 1)
    (hxc : |(x.toVal : ℝ) - x₀| ≤ tableError)
    (hyc : |(y.toVal : ℝ) - y₀| ≤ tableError) :
    |((roundedProduct x y).toVal : ℝ) - x₀ * y₀| ≤ (4 : ℝ) / 1000000 := by
  have hxy : |(x.toVal : ℝ) * y.toVal| ≤ 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (x.toVal : ℝ), abs_nonneg (y.toVal : ℝ)]
  have hround := round_error_le_micro ((x.toVal : ℝ) * y.toVal) (hxy.trans (by norm_num))
  have hstored := stored_mul_close hy hx₀ hxc hyc
  calc
    |((roundedProduct x y).toVal : ℝ) - x₀ * y₀| ≤
        |((roundedProduct x y).toVal : ℝ) - (x.toVal : ℝ) * y.toVal| +
          |(x.toVal : ℝ) * y.toVal - x₀ * y₀| := by
            calc
              |((roundedProduct x y).toVal : ℝ) - x₀ * y₀| =
                  |(((roundedProduct x y).toVal : ℝ) - (x.toVal : ℝ) * y.toVal) +
                    ((x.toVal : ℝ) * y.toVal - x₀ * y₀)| := by
                      congr 1
                      ring
              _ ≤ _ := abs_add_le _ _
    _ ≤ (1 : ℝ) / 1000000 + 3 / 1000000 := add_le_add hround hstored
    _ = (4 : ℝ) / 1000000 := by norm_num

/-- The rounded bilinear block approximates `x₀y₀ + z₀w₀` to `10⁻⁵`. -/
private theorem roundedBilinear_close
    {x y z w : FiniteFp} {x₀ y₀ z₀ w₀ : ℝ}
    (hx : |(x.toVal : ℝ)| ≤ 2) (hy : |(y.toVal : ℝ)| ≤ 2)
    (hz : |(z.toVal : ℝ)| ≤ 2) (hw : |(w.toVal : ℝ)| ≤ 2)
    (hx₀ : |x₀| ≤ 1) (hz₀ : |z₀| ≤ 1) (hw₀ : |w₀| ≤ 1)
    (hxc : |(x.toVal : ℝ) - x₀| ≤ tableError)
    (hyc : |(y.toVal : ℝ) - y₀| ≤ tableError)
    (hzc : |(z.toVal : ℝ) - z₀| ≤ tableError)
    (hwc : |(w.toVal : ℝ) - w₀| ≤ tableError) :
    |((roundedBilinear x y z w).toVal : ℝ) - (x₀ * y₀ + z₀ * w₀)| ≤ compositionError := by
  let q := roundedProduct z w
  have hqclose : |(q.toVal : ℝ) - z₀ * w₀| ≤ (4 : ℝ) / 1000000 :=
    roundedProduct_close hz hw hz₀ hzc hwc
  have hqabs : |(q.toVal : ℝ)| ≤ 2 := by
    have hdiff := abs_sub_abs_le_abs_sub (q.toVal : ℝ) (z₀ * w₀)
    have hzw : |z₀ * w₀| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg z₀, abs_nonneg w₀]
    linarith
  have hxy : |(x.toVal : ℝ) * y.toVal| ≤ 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (x.toVal : ℝ), abs_nonneg (y.toVal : ℝ)]
  have hfmaArg : |(x.toVal : ℝ) * y.toVal + q.toVal| ≤ 6 := by
    exact (abs_add_le _ _).trans (by linarith)
  have hfmaRound := round_error_le_micro
    ((x.toVal : ℝ) * y.toVal + q.toVal) (hfmaArg.trans (by norm_num))
  change |((roundedBilinear x y z w).toVal : ℝ) -
    ((x.toVal : ℝ) * y.toVal + q.toVal)| ≤ (1 : ℝ) / 1000000 at hfmaRound
  have hxyclose := stored_mul_close hy hx₀ hxc hyc
  calc
    |((roundedBilinear x y z w).toVal : ℝ) - (x₀ * y₀ + z₀ * w₀)| =
        |(((roundedBilinear x y z w).toVal : ℝ) -
            ((x.toVal : ℝ) * y.toVal + q.toVal)) +
          (((x.toVal : ℝ) * y.toVal - x₀ * y₀) + ((q.toVal : ℝ) - z₀ * w₀))| := by
            congr 1
            ring
    _ ≤ |((roundedBilinear x y z w).toVal : ℝ) -
            ((x.toVal : ℝ) * y.toVal + q.toVal)| +
          |((x.toVal : ℝ) * y.toVal - x₀ * y₀) + ((q.toVal : ℝ) - z₀ * w₀)| :=
      abs_add_le _ _
    _ ≤ |((roundedBilinear x y z w).toVal : ℝ) -
            ((x.toVal : ℝ) * y.toVal + q.toVal)| +
          (|(x.toVal : ℝ) * y.toVal - x₀ * y₀| + |(q.toVal : ℝ) - z₀ * w₀|) :=
      add_le_add (le_refl _) (abs_add_le _ _)
    _ = |((roundedBilinear x y z w).toVal : ℝ) -
            ((x.toVal : ℝ) * y.toVal + q.toVal)| +
          |(x.toVal : ℝ) * y.toVal - x₀ * y₀| + |(q.toVal : ℝ) - z₀ * w₀| := by ring
    _ ≤ (1 : ℝ) / 1000000 + 3 / 1000000 + 4 / 1000000 := by
      exact add_le_add (add_le_add hfmaRound hxyclose) hqclose
    _ ≤ compositionError := by norm_num [compositionError]

/-! ## Pair-input feature construction -/

noncomputable def cosCoordinate {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (i : Fin n) : FiniteFp :=
  roundedBilinear
    (entry B a (Fin.castAdd n i)) (entry B b (Fin.castAdd n i))
    (-entry B a (Fin.natAdd n i)) (entry B b (Fin.natAdd n i))

noncomputable def sinCoordinate {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (i : Fin n) : FiniteFp :=
  roundedBilinear
    (entry B a (Fin.natAdd n i)) (entry B b (Fin.castAdd n i))
    (entry B a (Fin.castAdd n i)) (entry B b (Fin.natAdd n i))

/-- The actual Binary32 feature computed from separate inputs `a` and `b`. -/
noncomputable def composedFeature {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) : Fin (n + n) → FiniteFp :=
  Fin.append (cosCoordinate B a b) (sinCoordinate B a b)

theorem cosCoordinate_close {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (i : Fin n) :
    |((cosCoordinate B a b i).toVal : ℝ) -
      Real.cos (phase (B.freq i) (a + b))| ≤ compositionError := by
  let ca := Real.cos (phase (B.freq i) a)
  let cb := Real.cos (phase (B.freq i) b)
  let sa := Real.sin (phase (B.freq i) a)
  let sb := Real.sin (phase (B.freq i) b)
  have hca : |((entry B a (Fin.castAdd n i)).toVal : ℝ) - ca| ≤ tableError := by
    simpa only [ca, FrequencyBank.feature, Fin.append_left] using
      entry_close B a (Fin.castAdd n i)
  have hcb : |((entry B b (Fin.castAdd n i)).toVal : ℝ) - cb| ≤ tableError := by
    simpa only [cb, FrequencyBank.feature, Fin.append_left] using
      entry_close B b (Fin.castAdd n i)
  have hsa : |((entry B a (Fin.natAdd n i)).toVal : ℝ) - sa| ≤ tableError := by
    simpa only [sa, FrequencyBank.feature, Fin.append_right] using
      entry_close B a (Fin.natAdd n i)
  have hsb : |((entry B b (Fin.natAdd n i)).toVal : ℝ) - sb| ≤ tableError := by
    simpa only [sb, FrequencyBank.feature, Fin.append_right] using
      entry_close B b (Fin.natAdd n i)
  have hnsa : |((-entry B a (Fin.natAdd n i)).toVal : ℝ) - (-sa)| ≤ tableError := by
    rw [FiniteFp.toVal_neg_eq_neg]
    have heq : -((entry B a (Fin.natAdd n i)).toVal : ℝ) - -sa =
        -(((entry B a (Fin.natAdd n i)).toVal : ℝ) - sa) := by ring
    rw [heq, abs_neg]
    exact hsa
  have h := roundedBilinear_close (x₀ := ca) (y₀ := cb) (z₀ := -sa) (w₀ := sb)
    (entry_abs_le_two B a (Fin.castAdd n i)) (entry_abs_le_two B b (Fin.castAdd n i))
    (by simpa [FiniteFp.toVal_neg_eq_neg] using entry_abs_le_two B a (Fin.natAdd n i))
    (entry_abs_le_two B b (Fin.natAdd n i))
    (abs_cos_le_one _) (by simpa using abs_sin_le_one (phase (B.freq i) a))
    (abs_sin_le_one _) hca hcb hnsa hsb
  simpa [cosCoordinate, ca, cb, sa, sb, cos_phase_add, Real.cos_add,
    sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h

theorem sinCoordinate_close {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (i : Fin n) :
    |((sinCoordinate B a b i).toVal : ℝ) -
      Real.sin (phase (B.freq i) (a + b))| ≤ compositionError := by
  let ca := Real.cos (phase (B.freq i) a)
  let cb := Real.cos (phase (B.freq i) b)
  let sa := Real.sin (phase (B.freq i) a)
  let sb := Real.sin (phase (B.freq i) b)
  have hca : |((entry B a (Fin.castAdd n i)).toVal : ℝ) - ca| ≤ tableError := by
    simpa only [ca, FrequencyBank.feature, Fin.append_left] using
      entry_close B a (Fin.castAdd n i)
  have hcb : |((entry B b (Fin.castAdd n i)).toVal : ℝ) - cb| ≤ tableError := by
    simpa only [cb, FrequencyBank.feature, Fin.append_left] using
      entry_close B b (Fin.castAdd n i)
  have hsa : |((entry B a (Fin.natAdd n i)).toVal : ℝ) - sa| ≤ tableError := by
    simpa only [sa, FrequencyBank.feature, Fin.append_right] using
      entry_close B a (Fin.natAdd n i)
  have hsb : |((entry B b (Fin.natAdd n i)).toVal : ℝ) - sb| ≤ tableError := by
    simpa only [sb, FrequencyBank.feature, Fin.append_right] using
      entry_close B b (Fin.natAdd n i)
  have h := roundedBilinear_close (x₀ := sa) (y₀ := cb) (z₀ := ca) (w₀ := sb)
    (entry_abs_le_two B a (Fin.natAdd n i)) (entry_abs_le_two B b (Fin.castAdd n i))
    (entry_abs_le_two B a (Fin.castAdd n i)) (entry_abs_le_two B b (Fin.natAdd n i))
    (abs_sin_le_one _) (abs_cos_le_one _) (abs_sin_le_one _)
    hsa hcb hca hsb
  simpa [sinCoordinate, ca, cb, sa, sb, sin_phase_add, Real.sin_add,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The separately computed pair feature approximates the exact feature of `a+b` coordinate-wise. -/
theorem composedFeature_close {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (j : Fin (n + n)) :
    |((composedFeature B a b j).toVal : ℝ) - B.feature (a + b) j| ≤ compositionError := by
  unfold composedFeature FrequencyBank.feature
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.append_left]
    exact cosCoordinate_close B a b i
  · rw [Fin.append_right, Fin.append_right]
    exact sinCoordinate_close B a b i

/-! ## Subnormal-safe sequential FMA readout -/

/-- Each readout FMA contributes at most `10⁻⁴` while its exact input magnitude is at most 1120. -/
private theorem round_error_le_dotStep (x : ℝ) (hx : |x| ≤ 1120) :
    |((round x).toVal : ℝ) - x| ≤ (1 : ℝ) / 10000 := by
  have h := round_error_le_unified x (small_bound_le_largest x hx)
  have hnum : (2 : ℝ) ^ (-24 : ℤ) * 1120 + (2 : ℝ) ^ (-150 : ℤ) ≤
      (1 : ℝ) / 10000 := by norm_num
  calc
    |((round x).toVal : ℝ) - x| ≤
        (2 : ℝ) ^ (-24 : ℤ) * |x| + (2 : ℝ) ^ (-150 : ℤ) := h
    _ ≤ (2 : ℝ) ^ (-24 : ℤ) * 1120 + (2 : ℝ) ^ (-150 : ℤ) := by gcongr
    _ ≤ (1 : ℝ) / 10000 := hnum

/-- Right-associated sequential FMA dot product.  Each step computes `round(x*y + accumulator)`;
there is no separately rounded multiplication. -/
noncomputable def dotFold : List (FiniteFp × FiniteFp) → FiniteFp
  | [] => 0
  | (x, y) :: rest => roundedFMA x y (dotFold rest)

/-- The exact real dot product corresponding to a pair list. -/
noncomputable def dotExact (pairs : List (FiniteFp × FiniteFp)) : ℝ :=
  (pairs.map fun q => (q.1.toVal : ℝ) * q.2.toVal).sum

/-- Simultaneous magnitude and forward-error invariant for the sequential FMA fold.  It is stated
with absolute error rather than a relative `γₙ` bound, so cancellation through subnormal values is
allowed. -/
private theorem dotFold_bounds (pairs : List (FiniteFp × FiniteFp))
    (hpair : ∀ q ∈ pairs, |(q.1.toVal : ℝ)| ≤ 2 ∧ |(q.2.toVal : ℝ)| ≤ 2)
    (hlen : pairs.length ≤ 224) :
    |((dotFold pairs).toVal : ℝ)| ≤ 5 * pairs.length ∧
    |((dotFold pairs).toVal : ℝ) - dotExact pairs| ≤ (pairs.length : ℝ) / 10000 := by
  induction pairs with
  | nil =>
      simp [dotFold, dotExact, FiniteFp.toVal_zero]
  | cons q rest ih =>
      obtain ⟨x, y⟩ := q
      have hhead := hpair (x, y) (by simp)
      have htail : ∀ q ∈ rest, |(q.1.toVal : ℝ)| ≤ 2 ∧ |(q.2.toVal : ℝ)| ≤ 2 := by
        intro q hq
        exact hpair q (by simp [hq])
      have hlenTail : rest.length ≤ 224 := by simpa using Nat.le_trans (Nat.le_succ _) hlen
      obtain ⟨hacc, herr⟩ := ih htail hlenTail
      let z : ℝ := (x.toVal : ℝ) * y.toVal + (dotFold rest).toVal
      have hprod : |(x.toVal : ℝ) * y.toVal| ≤ 4 := by
        rw [abs_mul]
        nlinarith [abs_nonneg (x.toVal : ℝ), abs_nonneg (y.toVal : ℝ)]
      have hz : |z| ≤ 5 * rest.length + 4 := by
        exact (abs_add_le _ _).trans (by linarith)
      have hz1120 : |z| ≤ 1120 := by
        simp only [List.length_cons] at hlen
        have hrest : rest.length ≤ 223 := by omega
        have hrestReal : (rest.length : ℝ) ≤ 223 := by exact_mod_cast hrest
        exact hz.trans (by linarith)
      have hlocal := round_error_le_dotStep z hz1120
      change |((roundedFMA x y (dotFold rest)).toVal : ℝ) - z| ≤
        (1 : ℝ) / 10000 at hlocal
      constructor
      · have hout : |((roundedFMA x y (dotFold rest)).toVal : ℝ)| ≤
            |((roundedFMA x y (dotFold rest)).toVal : ℝ) - z| + |z| := by
          calc
            |((roundedFMA x y (dotFold rest)).toVal : ℝ)| =
                |(((roundedFMA x y (dotFold rest)).toVal : ℝ) - z) + z| := by
                  congr 1
                  ring
            _ ≤ _ := abs_add_le _ _
        simpa [dotFold] using
          (hout.trans (by linarith))
      · have hdecomp :
            ((roundedFMA x y (dotFold rest)).toVal : ℝ) -
                ((x.toVal : ℝ) * y.toVal + dotExact rest) =
              (((roundedFMA x y (dotFold rest)).toVal : ℝ) - z) +
                (((dotFold rest).toVal : ℝ) - dotExact rest) := by
          dsimp [z]
          ring
        change |((roundedFMA x y (dotFold rest)).toVal : ℝ) -
            ((x.toVal : ℝ) * y.toVal + dotExact rest)| ≤
          (((rest.length + 1 : ℕ) : ℝ) / 10000)
        rw [hdecomp]
        calc
          |((roundedFMA x y (dotFold rest)).toVal : ℝ) - z +
              ((dotFold rest).toVal - dotExact rest)| ≤
              |((roundedFMA x y (dotFold rest)).toVal : ℝ) - z| +
                |((dotFold rest).toVal : ℝ) - dotExact rest| := abs_add_le _ _
          _ ≤ (1 : ℝ) / 10000 + (rest.length : ℝ) / 10000 :=
            add_le_add hlocal herr
          _ = ((rest.length + 1 : ℕ) : ℝ) / 10000 := by push_cast; ring

private theorem compositionError_le_one : compositionError ≤ 1 := by
  norm_num [compositionError]

/-- Every separately composed Binary32 feature coordinate has magnitude at most two. -/
theorem composedFeature_abs_le_two {p n : ℕ} [Fact p.Prime]
    (B : FrequencyBank p n) (a b : ZMod p) (j : Fin (n + n)) :
    |((composedFeature B a b j).toVal : ℝ)| ≤ 2 := by
  have hclose := composedFeature_close B a b j
  have hdiff := abs_sub_abs_le_abs_sub
    ((composedFeature B a b j).toVal : ℝ) (B.feature (a + b) j)
  have hideal := B.abs_feature_le_one (a + b) j
  linarith [compositionError_le_one]

/-- The 224 readout pairs for an actual input pair and candidate class. -/
noncomputable def fullPairs113 (a b c : ZMod 113) : List (FiniteFp × FiniteFp) :=
  List.ofFn fun j => (fullTables113.readout c j, composedFeature fullBank113 a b j)

@[simp] theorem fullPairs113_length (a b c : ZMod 113) : (fullPairs113 a b c).length = 224 := by
  unfold fullPairs113
  exact List.length_ofFn

private theorem fullPairs113_operand_bounds (a b c : ZMod 113) :
    ∀ q ∈ fullPairs113 a b c, |(q.1.toVal : ℝ)| ≤ 2 ∧ |(q.2.toVal : ℝ)| ≤ 2 := by
  intro q hq
  simp only [fullPairs113, List.mem_ofFn] at hq
  obtain ⟨j, rfl⟩ := hq
  exact ⟨by
    rw [fullTables113_readout]
    exact entry_abs_le_two fullBank113 c j,
    composedFeature_abs_le_two fullBank113 a b j⟩

/-- The actual end-to-end Binary32 logit for inputs `a,b` and candidate class `c`. -/
noncomputable def endToEndLogit113 (a b c : ZMod 113) : ℝ :=
  (dotFold (fullPairs113 a b c)).toVal

/-- The sequential FMA readout contributes at most `224/10000` absolute error against the dot
product of the stored readout and separately composed input feature. -/
theorem endToEndLogit113_arithmetic_error (a b c : ZMod 113) :
    |endToEndLogit113 a b c -
      ∑ j, ((fullTables113.readout c j).toVal : ℝ) *
        ((composedFeature fullBank113 a b j).toVal : ℝ)| ≤ (224 : ℝ) / 10000 := by
  have h := (dotFold_bounds (fullPairs113 a b c) (fullPairs113_operand_bounds a b c)
    (by simp)).2
  rw [fullPairs113_length] at h
  have hdexact : dotExact (fullPairs113 a b c) =
      ∑ j, ((fullTables113.readout c j).toVal : ℝ) *
        ((composedFeature fullBank113 a b j).toVal : ℝ) := by
    rw [dotExact, fullPairs113, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [endToEndLogit113, ← hdexact]
  exact h

/-- Quantization and pair-composition error in the 224 stored products. -/
theorem endToEndLogit113_feature_error (a b c : ZMod 113) :
    |(∑ j, ((fullTables113.readout c j).toVal : ℝ) *
        ((composedFeature fullBank113 a b j).toVal : ℝ)) -
      clockLogit fullBank113.toFinset (a + b) c| ≤
        (224 : ℝ) * (2 * tableError + compositionError) := by
  have hterm : ∀ j : Fin 224,
      |((fullTables113.readout c j).toVal : ℝ) *
          ((composedFeature fullBank113 a b j).toVal : ℝ) -
        fullBank113.readoutRow c j * fullBank113.feature (a + b) j| ≤
          2 * tableError + compositionError := by
    intro j
    have hr := fullTables113_readout_close c j
    have hx := composedFeature_close fullBank113 a b j
    have hxabs := composedFeature_abs_le_two fullBank113 a b j
    have hr0 : |fullBank113.readoutRow c j| ≤ 1 := by
      simpa only [FrequencyBank.readoutRow] using fullBank113.abs_feature_le_one c j
    calc
      |((fullTables113.readout c j).toVal : ℝ) *
          ((composedFeature fullBank113 a b j).toVal : ℝ) -
        fullBank113.readoutRow c j * fullBank113.feature (a + b) j| =
        |(((fullTables113.readout c j).toVal : ℝ) - fullBank113.readoutRow c j) *
            ((composedFeature fullBank113 a b j).toVal : ℝ) +
          fullBank113.readoutRow c j *
            (((composedFeature fullBank113 a b j).toVal : ℝ) -
              fullBank113.feature (a + b) j)| := by ring_nf
      _ ≤ |(((fullTables113.readout c j).toVal : ℝ) - fullBank113.readoutRow c j) *
              ((composedFeature fullBank113 a b j).toVal : ℝ)| +
            |fullBank113.readoutRow c j *
              (((composedFeature fullBank113 a b j).toVal : ℝ) -
                fullBank113.feature (a + b) j)| := abs_add_le _ _
      _ = |((fullTables113.readout c j).toVal : ℝ) - fullBank113.readoutRow c j| *
              |((composedFeature fullBank113 a b j).toVal : ℝ)| +
            |fullBank113.readoutRow c j| *
              |((composedFeature fullBank113 a b j).toVal : ℝ) -
                fullBank113.feature (a + b) j| := by rw [abs_mul, abs_mul]
      _ ≤ tableError * 2 + 1 * compositionError := by
        exact add_le_add
          (mul_le_mul hr hxabs (abs_nonneg _) tableError_nonneg)
          (mul_le_mul hr0 hx (abs_nonneg _) (by norm_num))
      _ = 2 * tableError + compositionError := by ring
  have hideal : (∑ j, fullBank113.readoutRow c j * fullBank113.feature (a + b) j) =
      clockLogit fullBank113.toFinset (a + b) c := by
    calc
      (∑ j, fullBank113.readoutRow c j * fullBank113.feature (a + b) j) =
          ∑ j, fullBank113.feature (a + b) j * fullBank113.readoutRow c j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [mul_comm]
      _ = _ := feature_dot_eq_clockLogit fullBank113 (a + b) c
  rw [← hideal, ← Finset.sum_sub_distrib]
  calc
    |∑ j, (((fullTables113.readout c j).toVal : ℝ) *
        ((composedFeature fullBank113 a b j).toVal : ℝ) -
      fullBank113.readoutRow c j * fullBank113.feature (a + b) j)| ≤
        ∑ j, |((fullTables113.readout c j).toVal : ℝ) *
          ((composedFeature fullBank113 a b j).toVal : ℝ) -
        fullBank113.readoutRow c j * fullBank113.feature (a + b) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 224, (2 * tableError + compositionError) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = (224 : ℝ) * (2 * tableError + compositionError) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

/-- Uniform per-logit error of the actual end-to-end Binary32 implementation. -/
noncomputable def endToEndError113 : ℝ :=
  (224 : ℝ) / 10000 + 224 * (2 * tableError + compositionError)

theorem endToEndLogit113_error (a b c : ZMod 113) :
    |endToEndLogit113 a b c - clockLogit fullBank113.toFinset (a + b) c| ≤
      endToEndError113 := by
  have ha := endToEndLogit113_arithmetic_error a b c
  have hf := endToEndLogit113_feature_error a b c
  calc
    |endToEndLogit113 a b c - clockLogit fullBank113.toFinset (a + b) c| ≤
        |endToEndLogit113 a b c -
          ∑ j, ((fullTables113.readout c j).toVal : ℝ) *
            ((composedFeature fullBank113 a b j).toVal : ℝ)| +
        |(∑ j, ((fullTables113.readout c j).toVal : ℝ) *
          ((composedFeature fullBank113 a b j).toVal : ℝ)) -
          clockLogit fullBank113.toFinset (a + b) c| := by
            calc
              |endToEndLogit113 a b c - clockLogit fullBank113.toFinset (a + b) c| =
                  |(endToEndLogit113 a b c -
                    ∑ j, ((fullTables113.readout c j).toVal : ℝ) *
                      ((composedFeature fullBank113 a b j).toVal : ℝ)) +
                  ((∑ j, ((fullTables113.readout c j).toVal : ℝ) *
                    ((composedFeature fullBank113 a b j).toVal : ℝ)) -
                    clockLogit fullBank113.toFinset (a + b) c)| := by
                      congr 1
                      ring
              _ ≤ _ := abs_add_le _ _
    _ ≤ (224 : ℝ) / 10000 + 224 * (2 * tableError + compositionError) := add_le_add ha hf
    _ = endToEndError113 := rfl

private theorem twice_endToEndError_lt_marginLower :
    2 * endToEndError113 < (896 : ℝ) / 12769 := by
  norm_num [endToEndError113, tableError, compositionError]

/-- **End-to-end strict argmax.** The implementation takes `a` and `b` separately, constructs their
sum feature in Binary32, evaluates all 224 readout coordinates with sequential FMA, and ranks the
true modular sum above every wrong class. -/
theorem endToEndLogit113_correct (a b : ZMod 113) :
    ∀ c, c ≠ a + b → endToEndLogit113 a b c < endToEndLogit113 a b (a + b) := by
  apply correct_under_perturbation fullBank113.toFinset (a + b) (endToEndLogit113 a b)
    endToEndError113 (endToEndLogit113_error a b)
  exact twice_endToEndError_lt_marginLower.trans_le (fullBank113_margin_lower (a + b))

/-- The actual Binary32 decoder has no failing input pairs. -/
theorem endToEndFailureSet113_eq_empty : FailureSet endToEndLogit113 = ∅ := by
  ext ⟨a, b⟩
  simp only [FailureSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact endToEndLogit113_correct a b

/-- **Headline result: the end-to-end full-bank Binary32 modular-addition clock at `p=113` has
certified accuracy one.** -/
theorem endToEndAccuracy113_eq_one : accuracy endToEndLogit113 = 1 := by
  rw [accuracy, endToEndFailureSet113_eq_empty, Set.ncard_empty]
  simp

end Flean.ModAddClock.Binary32
