import Flean.IntegerEquivalence.UlpPow2
import Flean.Rounding.Neighbor.Order
import Flean.Rounding.Neighbor.Properties

/-! # FP ↔ Integer equivalence: structural successor (positive case)

Phase 1.6 of the FP ↔ Integer equivalence area
(see `.claude/notes/fp-integer-equivalence.md`).

For positive `f : FiniteFp`, the **successor** is the smallest representable
value strictly greater than `f`. Three structural cases:

1. *Within-binade*: `f.m + 1 < 2^prec`. Successor is `⟨false, f.e, f.m + 1⟩`.
   Covers: positive subnormal step, subnormal→normal transition, and normal
   step within a binade.
2. *Cross-binade*: `f.m + 1 = 2^prec` and `f.e + 1 ≤ max_exp`. Successor is
   `⟨false, f.e + 1, 2^(prec-1)⟩` (significand carry into the next binade).
3. *Saturation*: `f = largestFiniteFloat`. Successor overflows to `+∞`.

In all three cases the value increases by exactly `2^(f.e - prec + 1)`,
which equals `Fp.ulp f.toVal` for non-saturated `f`. This is the value-level
statement of "next FP = FP + ulp" — the foundation for the bit-level
"next FP bit pattern = bit pattern + 1" bridge.

The negative-input case (`f.s = true`) is a natural follow-up — for
negative `f`, the successor moves *toward* zero (so the magnitude is
*decremented*, not incremented), with the `-0 → +smallestSubnormal`
sign-crossing as a special case.
-/

namespace FiniteFp

variable [FloatFormat]

/-! ## Validity helpers -/

/-- Validity of `⟨false, f.e, f.m + 1, _⟩` when `f.m + 1 < 2^prec`.
The classification (normal vs subnormal) follows from `f`'s own
classification: a normal `f` stays normal after incrementing the
significand; a subnormal `f` either stays subnormal or transitions to the
smallest normal at the same `min_exp`. -/
private theorem successor_within_valid {f : FiniteFp}
    (hsmax : f.m + 1 < 2^FloatFormat.prec.toNat) :
    IsValidFiniteVal f.e (f.m + 1) := by
  refine ⟨f.valid.1, f.valid.2.1, hsmax, ?_⟩
  rcases f.valid.2.2.2 with hn | hsub
  · -- f normal: m ≥ 2^(prec-1), so m+1 ≥ 2^(prec-1) too
    left
    refine ⟨?_, hsmax⟩
    have h1 := hn.1
    omega
  · -- f subnormal: e = min_exp. Two sub-cases.
    by_cases h : 2^(FloatFormat.prec - 1).toNat ≤ f.m + 1
    · left
      exact ⟨h, hsmax⟩
    · right
      refine ⟨hsub.1, ?_⟩
      omega

/-- Validity of `⟨false, f.e + 1, 2^(prec-1)⟩` when `f.e + 1 ≤ max_exp`. -/
private theorem successor_cross_valid {f : FiniteFp}
    (he_lt : f.e + 1 ≤ FloatFormat.max_exp) :
    IsValidFiniteVal (f.e + 1) (2^(FloatFormat.prec - 1).toNat) := by
  refine ⟨?_, he_lt,
    FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec, Or.inl isNormal.sig_msb⟩
  have := f.valid.1
  omega

/-! ## Definition of the structural successor -/

/-- **Structural successor of a positive `f`.** Returns `+∞` at saturation
(`f = largestFiniteFloat`). Defined uniformly via the case split on
mantissa overflow + exponent saturation; the sign of the result is always
`false` (the only way `successor` can change sign is for a negative input,
which this definition does not handle — see file docstring). -/
def successorPos (f : FiniteFp) : Fp :=
  if hsmax : f.m + 1 < 2^FloatFormat.prec.toNat then
    Fp.finite ⟨false, f.e, f.m + 1, successor_within_valid hsmax⟩
  else if hemax : f.e + 1 ≤ FloatFormat.max_exp then
    Fp.finite ⟨false, f.e + 1, 2^(FloatFormat.prec - 1).toNat,
      successor_cross_valid hemax⟩
  else
    Fp.infinite false

/-! ## Value-level computation -/

/-- For positive `f`, the within-binade successor's value increases by
exactly `2^(f.e - prec + 1)`. -/
theorem successorPos_within_toVal {R : Type*} [Field R]
    (f : FiniteFp) (hs : f.s = false)
    (hsmax : f.m + 1 < 2^FloatFormat.prec.toNat) :
    let g : FiniteFp := ⟨false, f.e, f.m + 1, successor_within_valid hsmax⟩
    (g.toVal : R) = (f.toVal : R) + (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
  simp only
  rw [FiniteFp.toVal_pos_eq _ rfl, FiniteFp.toVal_pos_eq f hs]
  push_cast
  ring

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- For positive `f` at the binade boundary, the cross-binade successor's
value increases by exactly `2^(f.e - prec + 1)`. -/
theorem successorPos_cross_toVal (f : FiniteFp) (hs : f.s = false)
    (hsmax : f.m + 1 = 2^FloatFormat.prec.toNat)
    (he_lt : f.e + 1 ≤ FloatFormat.max_exp) :
    let g : FiniteFp := ⟨false, f.e + 1, 2^(FloatFormat.prec - 1).toNat,
      successor_cross_valid he_lt⟩
    (g.toVal : R) = (f.toVal : R) + (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
  simp only
  rw [FiniteFp.toVal_pos_eq _ rfl, FiniteFp.toVal_pos_eq f hs]
  -- Normalize ↑(2^k) to (2 : R)^k for both sides
  have htwo_ne : (2 : R) ≠ 0 := by norm_num
  -- Rewrite the LHS Nat-power-cast as a R-power-cast at the natCast exponent
  rw [show (((2 : ℕ) ^ (FloatFormat.prec - 1).toNat : ℕ) : R)
        = (2 : R) ^ ((FloatFormat.prec - 1).toNat : ℤ) from by
        rw [zpow_natCast]; push_cast; rfl]
  rw [FloatFormat.prec_sub_one_toNat_eq]
  -- LHS now: 2^(prec-1) * 2^(f.e + 1 - prec + 1)
  -- Use hsmax (cast to R) on the RHS: ↑(f.m + 1) = ↑(2^prec.toNat)
  have hcast : ((f.m + 1 : ℕ) : R) = (2 : R) ^ (FloatFormat.prec : ℤ) := by
    rw [hsmax]
    rw [show (FloatFormat.prec : ℤ) = (FloatFormat.prec.toNat : ℤ) from
          FloatFormat.prec_toNat_eq.symm, zpow_natCast]
    push_cast; rfl
  -- Factor the RHS as ((f.m : R) + 1) * 2^(f.e - prec + 1)
  rw [show (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)
          + (2 : R) ^ (f.e - FloatFormat.prec + 1)
        = ((f.m : R) + 1) * (2 : R) ^ (f.e - FloatFormat.prec + 1) from by ring]
  rw [show ((f.m : R) + 1) = ((f.m + 1 : ℕ) : R) from by push_cast; ring,
      hcast,
      ← zpow_add₀ htwo_ne, ← zpow_add₀ htwo_ne]
  congr 1
  ring

/-- **Master value-level computation.** When `successorPos f` is finite
(i.e., `f` is not saturated), its value equals `f.toVal + 2^(f.e - prec + 1)`. -/
theorem successorPos_toVal_of_finite (f : FiniteFp) (hs : f.s = false)
    {g : FiniteFp} (hg : successorPos f = Fp.finite g) :
    (g.toVal : R) = (f.toVal : R) + (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
  unfold successorPos at hg
  split_ifs at hg with hsmax hemax
  · -- Within-binade: hg has the structural form on the LHS
    have h_eq : g = ⟨false, f.e, f.m + 1, successor_within_valid hsmax⟩ :=
      (Fp.finite.inj hg).symm
    rw [h_eq]
    exact successorPos_within_toVal (R := R) f hs hsmax
  · -- Cross-binade
    have h_eq : g = ⟨false, f.e + 1, 2^(FloatFormat.prec - 1).toNat,
        successor_cross_valid hemax⟩ :=
      (Fp.finite.inj hg).symm
    have hsmax' : f.m + 1 = 2^FloatFormat.prec.toNat := by
      have h1 : f.m + 1 ≤ 2^FloatFormat.prec.toNat := by
        have := f.valid.2.2.1; omega
      omega
    rw [h_eq]
    exact successorPos_cross_toVal (R := R) f hs hsmax' hemax

/-! ## Saturation characterization -/

/-- Reverse direction of the saturation iff: at `largestFiniteFloat`,
`successorPos` overflows to `+∞`. -/
theorem successorPos_largest_eq_inf (f : FiniteFp)
    (hm : f.m + 1 = 2^FloatFormat.prec.toNat)
    (he : f.e = FloatFormat.max_exp) :
    successorPos f = Fp.infinite false := by
  unfold successorPos
  have hsmax_neg : ¬f.m + 1 < 2^FloatFormat.prec.toNat := by omega
  have hemax_neg : ¬f.e + 1 ≤ FloatFormat.max_exp := by omega
  rw [dif_neg hsmax_neg, dif_neg hemax_neg]

/-! ## Negative case: successor moves toward zero

For negative `f` (`f.s = true`), the successor moves *toward* zero (less
negative). The dispatch is:

1. *Negative zero* (`f.m = 0`): `-0` → smallest positive subnormal
   (sign-cross). IEEE 754 §6.3.
2. *Cross-binade descent* (`f.m = 2^(prec-1)` and `f.e > min_exp`):
   smallest-magnitude entry of binade → max-magnitude entry of next-down
   binade. Result: `⟨true, f.e - 1, 2^prec - 1⟩`.
3. *Within-binade descent*: decrement magnitude. Result:
   `⟨true, f.e, f.m - 1⟩`. Covers all other negative-with-positive-`m`
   cases, including the `-smallestPosNormal → -largestPosSubnormal`
   transition (still at `min_exp`). -/

private theorem successor_neg_within_valid {f : FiniteFp}
    (hm_pos : 0 < f.m)
    (hcase : f.m ≠ 2^(FloatFormat.prec - 1).toNat ∨ f.e = FloatFormat.min_exp) :
    IsValidFiniteVal f.e (f.m - 1) := by
  refine ⟨f.valid.1, f.valid.2.1, by have := f.valid.2.2.1; omega, ?_⟩
  -- Case-split on whether f.m - 1 ≥ 2^(prec-1) (normal) or < (subnormal)
  by_cases h_norm : 2^(FloatFormat.prec - 1).toNat ≤ f.m - 1
  · left; refine ⟨h_norm, by have := f.valid.2.2.1; omega⟩
  · right
    push_neg at h_norm
    -- f.m ≤ 2^(prec-1)
    have hf_e : f.e = FloatFormat.min_exp := by
      rcases f.valid.2.2.2 with hn | hsub
      · have hm_eq : f.m = 2^(FloatFormat.prec - 1).toNat := by
          have := hn.1; omega
        rcases hcase with h_ne | h_emin
        · exact absurd hm_eq h_ne
        · exact h_emin
      · exact hsub.1
    refine ⟨hf_e, by omega⟩

private theorem successor_neg_cross_valid {f : FiniteFp}
    (he_lt : FloatFormat.min_exp < f.e) :
    IsValidFiniteVal (f.e - 1) (2^FloatFormat.prec.toNat - 1) := by
  have hpos : 0 < (2 : ℕ) ^ FloatFormat.prec.toNat := Nat.two_pow_pos _
  have hpec_lt := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
  refine ⟨by have := f.valid.1; omega, by have := f.valid.2.1; omega,
    by omega, Or.inl isNormal.sig_max⟩

/-- **Structural successor for negative `f` (s = true).**

Mirrors `successorPos`: case-splits on whether decrementing the mantissa
needs to descend a binade, with the `-0 → +smallestPosSubnormal`
sign-cross as a special case. Always returns finite (the negative side
never overflows — `-largestFiniteFloat` has plenty of room toward zero). -/
def successorNeg (f : FiniteFp) : Fp :=
  if hzero : f.m = 0 then
    -- -0: sign-cross to +smallestPosSubnormal
    Fp.finite FiniteFp.smallestPosSubnormal
  else if hcross : f.m = 2^(FloatFormat.prec - 1).toNat ∧ FloatFormat.min_exp < f.e then
    -- Cross-binade descent: ⟨true, f.e - 1, 2^prec - 1⟩
    Fp.finite ⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1,
      successor_neg_cross_valid hcross.2⟩
  else
    -- Within-binade descent: ⟨true, f.e, f.m - 1⟩
    have hcase : f.m ≠ 2^(FloatFormat.prec - 1).toNat ∨ f.e = FloatFormat.min_exp := by
      push_neg at hcross
      by_cases hm : f.m = 2^(FloatFormat.prec - 1).toNat
      · right
        have := hcross hm
        have := f.valid.1
        omega
      · left; exact hm
    Fp.finite ⟨true, f.e, f.m - 1,
      successor_neg_within_valid (by omega) hcase⟩

/-- For negative `f` with the within-binade case (`f.m > 0` and not at the
binade boundary needing descent), the successor's value increases by
`2^(f.e - prec + 1)` (equivalently, magnitude decreases by ulp). -/
theorem successorNeg_within_toVal {R : Type*} [Field R]
    (f : FiniteFp) (hs : f.s = true)
    (hm_pos : 0 < f.m)
    (hcase : f.m ≠ 2^(FloatFormat.prec - 1).toNat ∨ f.e = FloatFormat.min_exp) :
    let g : FiniteFp := ⟨true, f.e, f.m - 1, successor_neg_within_valid hm_pos hcase⟩
    (g.toVal : R) = (f.toVal : R) + (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
  simp only
  -- Compute f.toVal: f negative ⇒ f.toVal = -((-f).toVal), and -f is positive.
  have hf_toVal : (f.toVal : R) = -((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) := by
    have h1 : f.toVal (R := R) = -((-f).toVal) := by
      rw [FiniteFp.toVal_neg_eq_neg]; ring
    rw [h1, FiniteFp.toVal_pos_eq (-f) (by simp [hs])]
    simp only [FiniteFp.neg_m, FiniteFp.neg_e]
  -- Compute g.toVal similarly: g = ⟨true, f.e, f.m - 1⟩, so -g = ⟨false, f.e, f.m - 1⟩.
  have hg_toVal :
      (⟨true, f.e, f.m - 1, successor_neg_within_valid hm_pos hcase⟩ : FiniteFp).toVal (R := R)
        = -(((f.m - 1 : ℕ) : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) := by
    set v := successor_neg_within_valid hm_pos hcase with hv_def
    have h_neg : (-⟨true, f.e, f.m - 1, v⟩ : FiniteFp)
        = ⟨false, f.e, f.m - 1, v⟩ := rfl
    have h_eq : (⟨true, f.e, f.m - 1, v⟩ : FiniteFp).toVal (R := R)
        = -(⟨false, f.e, f.m - 1, v⟩ : FiniteFp).toVal := by
      rw [← h_neg, FiniteFp.toVal_neg_eq_neg]; ring
    rw [h_eq, FiniteFp.toVal_pos_eq _ rfl]
  rw [hg_toVal, hf_toVal]
  rw [show ((f.m - 1 : ℕ) : R) = (f.m : R) - 1 from by
        rw [Nat.cast_sub (by omega : 1 ≤ f.m)]; push_cast; rfl]
  ring

/-- `successorNeg` evaluates to the within-binade descent in the
non-saturated, non-binade-boundary case. -/
theorem successorNeg_toVal_of_within (f : FiniteFp)
    (hm_pos : 0 < f.m)
    (hcase : f.m ≠ 2^(FloatFormat.prec - 1).toNat ∨ f.e = FloatFormat.min_exp) :
    successorNeg f =
      Fp.finite ⟨true, f.e, f.m - 1, successor_neg_within_valid hm_pos hcase⟩ := by
  unfold successorNeg
  have hzero_neg : ¬ f.m = 0 := by omega
  rw [dif_neg hzero_neg]
  by_cases hm : f.m = 2^(FloatFormat.prec - 1).toNat
  · rcases hcase with hne | he_min
    · exact absurd hm hne
    · have hcross_neg :
          ¬(f.m = 2 ^ (FloatFormat.prec - 1).toNat ∧ FloatFormat.min_exp < f.e) := by
        intro ⟨_, hgt⟩; omega
      rw [dif_neg hcross_neg]
  · have hcross_neg :
        ¬(f.m = 2 ^ (FloatFormat.prec - 1).toNat ∧ FloatFormat.min_exp < f.e) := by
      intro ⟨h1, _⟩; exact hm h1
    rw [dif_neg hcross_neg]

/-- `successorNeg` at `-0` is the smallest positive subnormal. -/
theorem successorNeg_neg_zero (f : FiniteFp) (hm : f.m = 0) :
    successorNeg f = Fp.finite FiniteFp.smallestPosSubnormal := by
  unfold successorNeg
  rw [dif_pos hm]

/-- For negative `f` at the binade boundary (`f.m = 2^(prec-1)` and
`f.e > min_exp`), `successorNeg` produces the cross-binade descent:
`⟨true, f.e - 1, 2^prec - 1⟩`. -/
theorem successorNeg_cross (f : FiniteFp)
    (hm : f.m = 2^(FloatFormat.prec - 1).toNat)
    (he : FloatFormat.min_exp < f.e) :
    successorNeg f = Fp.finite ⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1,
      successor_neg_cross_valid he⟩ := by
  unfold successorNeg
  have hm_ne : f.m ≠ 0 := by
    have hpos : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.two_pow_pos _
    omega
  rw [dif_neg hm_ne, dif_pos ⟨hm, he⟩]

/-- Cross-binade value computation: the successor's toVal increases by
`2^(f.e - prec)` — *half* the within-binade ulp. This asymmetry reflects
how the IEEE 754 binade boundaries work: at `-2^k` (negative side), the
gap toward zero is governed by the *smaller* binade `[-2^k, -2^(k-1))`,
which has ulp `2^(k - prec)`, half the ulp `2^(k - prec + 1)` of the
*larger* binade `[-2^(k+1), -2^k)`. -/
theorem successorNeg_cross_toVal {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (f : FiniteFp) (hs : f.s = true)
    (hm : f.m = 2^(FloatFormat.prec - 1).toNat)
    (he : FloatFormat.min_exp < f.e) :
    let g : FiniteFp := ⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1,
      successor_neg_cross_valid he⟩
    (g.toVal : R) = (f.toVal : R) + (2 : R) ^ (f.e - FloatFormat.prec) := by
  simp only
  have htwo_ne : (2 : R) ≠ 0 := by norm_num
  -- f.toVal = -(f.m * 2^(f.e - prec + 1))
  have hf_toVal : (f.toVal : R) = -((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) := by
    have h1 : f.toVal (R := R) = -((-f).toVal) := by
      rw [FiniteFp.toVal_neg_eq_neg]; ring
    rw [h1, FiniteFp.toVal_pos_eq (-f) (by simp [hs])]
    simp only [FiniteFp.neg_m, FiniteFp.neg_e]
  -- g.toVal = -((2^prec.toNat - 1) * 2^(f.e - 1 - prec + 1))
  have hg_toVal :
      (⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1, successor_neg_cross_valid he⟩
        : FiniteFp).toVal (R := R)
        = -((((2 : ℕ) ^ FloatFormat.prec.toNat - 1 : ℕ) : R)
            * (2 : R) ^ (f.e - 1 - FloatFormat.prec + 1)) := by
    set v := successor_neg_cross_valid he with hv_def
    have h_neg : (-⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1, v⟩ : FiniteFp)
        = ⟨false, f.e - 1, 2^FloatFormat.prec.toNat - 1, v⟩ := rfl
    have h_eq :
        (⟨true, f.e - 1, 2^FloatFormat.prec.toNat - 1, v⟩ : FiniteFp).toVal (R := R)
          = -(⟨false, f.e - 1, 2^FloatFormat.prec.toNat - 1, v⟩ : FiniteFp).toVal := by
      rw [← h_neg, FiniteFp.toVal_neg_eq_neg]; ring
    rw [h_eq, FiniteFp.toVal_pos_eq _ rfl]
  rw [hg_toVal, hf_toVal, hm]
  -- Goal: -((2^prec - 1) * 2^(f.e - prec))
  --     = -(2^(prec-1) * 2^(f.e - prec + 1)) + 2^(f.e - prec)
  -- Compute: (2^prec - 1) on R as (2^prec.toNat - 1 : ℕ).
  have hcast_prec : (((2 : ℕ) ^ FloatFormat.prec.toNat - 1 : ℕ) : R)
      = (2 : R) ^ (FloatFormat.prec : ℤ) - 1 := by
    have hpos : 1 ≤ (2 : ℕ) ^ FloatFormat.prec.toNat := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [Nat.cast_sub hpos]
    push_cast
    rw [show (FloatFormat.prec : ℤ) = (FloatFormat.prec.toNat : ℤ) from
          FloatFormat.prec_toNat_eq.symm, zpow_natCast]
    rfl
  rw [hcast_prec]
  rw [show (((2 : ℕ) ^ (FloatFormat.prec - 1).toNat : ℕ) : R)
        = (2 : R) ^ ((FloatFormat.prec - 1) : ℤ) from by
        rw [show ((FloatFormat.prec - 1 : ℤ)) =
              ((FloatFormat.prec - 1).toNat : ℤ) from
            FloatFormat.prec_sub_one_toNat_eq.symm,
            zpow_natCast]
        push_cast; rfl]
  -- Now exponent identity: 2^(prec-1) * 2^(f.e - prec + 1) = 2^prec * 2^(f.e - prec)
  -- And (2^prec - 1) * 2^(f.e - prec) = 2^prec * 2^(f.e - prec) - 2^(f.e - prec)
  --                                   = 2^(prec-1) * 2^(f.e - prec + 1) - 2^(f.e - prec)
  rw [show (f.e - 1 - FloatFormat.prec + 1 : ℤ) = f.e - FloatFormat.prec from by ring]
  -- LHS: -((2^prec - 1) * 2^(f.e - prec))
  -- RHS: -(2^(prec-1) * 2^(f.e - prec + 1)) + 2^(f.e - prec)
  -- Combine the powers: 2^(prec-1) * 2^(f.e - prec + 1) = 2^((prec-1) + (f.e - prec + 1)) = 2^f.e
  --                     2^prec * 2^(f.e - prec) = 2^(prec + f.e - prec) = 2^f.e
  --                     2^(f.e - prec + 1) = 2^(f.e - prec) * 2 = 2 * 2^(f.e - prec)
  -- LHS = -(2^prec * 2^(f.e - prec) - 2^(f.e - prec)) = -2^f.e + 2^(f.e - prec)
  -- RHS = -2^f.e + 2^(f.e - prec). ✓
  rw [show ((FloatFormat.prec - 1 : ℤ)) = FloatFormat.prec + (-1) from by ring,
      zpow_add₀ htwo_ne, mul_assoc, ← zpow_add₀ htwo_ne]
  rw [show ((-1 : ℤ) + (f.e - FloatFormat.prec + 1)) = f.e - FloatFormat.prec from by ring]
  ring

end FiniteFp

/-! ## Adjacency: `successorPos` is the immediate successor

For positive `f`, no representable value lies strictly between `f` and
`successorPos f`. This is the value-side bridge to `nextUp`: combined with
the existing `finite_lt_nextUp` and `nextUp_no_float_between` infrastructure,
adjacency forces `nextUp (Fp.finite f) = successorPos f`. -/

namespace FiniteFp

variable [FloatFormat]

/-! ### Helper bounds on positive toVal -/

/-- Cast helper: `(2 : R) ^ prec.toNat = 2^prec : R` (in zpow form). -/
private theorem two_natPow_prec_eq_zpow
    {R : Type*} [Field R] :
    ((2 : R) ^ FloatFormat.prec.toNat : R) = (2 : R) ^ (FloatFormat.prec : ℤ) := by
  rw [show (FloatFormat.prec : ℤ) = (FloatFormat.prec.toNat : ℤ) from
        FloatFormat.prec_toNat_eq.symm, zpow_natCast]
  rfl

/-- Cast helper: `(2 : R) ^ (prec-1).toNat = 2^(prec-1) : R` (in zpow form). -/
private theorem two_natPow_prec_sub_one_eq_zpow
    {R : Type*} [Field R] :
    ((2 : R) ^ (FloatFormat.prec - 1).toNat : R)
      = (2 : R) ^ ((FloatFormat.prec - 1) : ℤ) := by
  rw [show ((FloatFormat.prec - 1 : ℤ)) = ((FloatFormat.prec - 1).toNat : ℤ) from
        FloatFormat.prec_sub_one_toNat_eq.symm, zpow_natCast]
  rfl

/-- For positive `f`, `f.toVal < 2^(f.e + 1)`. -/
private theorem toVal_lt_two_zpow_succ (f : FiniteFp) (hs : f.s = false) :
    (f.toVal : ℚ) < (2 : ℚ) ^ (f.e + 1) := by
  rw [FiniteFp.toVal_pos_eq f hs]
  have hm_lt : (f.m : ℚ) < (2 : ℚ) ^ (FloatFormat.prec : ℤ) := by
    have hcast : (f.m : ℚ) < (2 : ℚ) ^ FloatFormat.prec.toNat := by
      exact_mod_cast f.valid.2.2.1
    rwa [two_natPow_prec_eq_zpow (R := ℚ)] at hcast
  have hzpos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
  have hcalc : (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
        < (2 : ℚ) ^ (FloatFormat.prec : ℤ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
    mul_lt_mul_of_pos_right hm_lt hzpos
  refine hcalc.trans_eq ?_
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1; ring

/-- For positive normal `f`, `2^f.e ≤ f.toVal`. -/
private theorem two_zpow_e_le_toVal_of_normal (f : FiniteFp) (hs : f.s = false)
    (hn : _root_.isNormal f.m) :
    (2 : ℚ) ^ f.e ≤ (f.toVal : ℚ) := by
  rw [FiniteFp.toVal_pos_eq f hs]
  have hm_ge : (2 : ℚ) ^ ((FloatFormat.prec - 1) : ℤ) ≤ (f.m : ℚ) := by
    have hcast : (2 : ℚ) ^ (FloatFormat.prec - 1).toNat ≤ (f.m : ℚ) := by
      exact_mod_cast hn.1
    rwa [two_natPow_prec_sub_one_eq_zpow (R := ℚ)] at hcast
  have hzpos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
  have hcalc : (2 : ℚ) ^ ((FloatFormat.prec - 1) : ℤ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
        ≤ (f.m : ℚ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
    mul_le_mul_of_nonneg_right hm_ge (le_of_lt hzpos)
  refine le_trans ?_ hcalc
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  apply le_of_eq
  congr 1; ring

/-- For positive subnormal `f`, `f.toVal < 2^min_exp`. -/
private theorem toVal_lt_two_zpow_min_of_subnormal (f : FiniteFp) (hs : f.s = false)
    (hsub : _root_.isSubnormal f.e f.m) :
    (f.toVal : ℚ) < (2 : ℚ) ^ FloatFormat.min_exp := by
  rw [FiniteFp.toVal_pos_eq f hs, hsub.1]
  have hm_lt : (f.m : ℚ) < (2 : ℚ) ^ ((FloatFormat.prec - 1) : ℤ) := by
    have hcast : (f.m : ℚ) < (2 : ℚ) ^ (FloatFormat.prec - 1).toNat := by
      have := hsub.2
      have hpos : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.two_pow_pos _
      exact_mod_cast (by omega : f.m < 2^(FloatFormat.prec - 1).toNat)
    rwa [two_natPow_prec_sub_one_eq_zpow (R := ℚ)] at hcast
  have hzpos : (0 : ℚ) < (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) := by positivity
  calc (f.m : ℚ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1)
      < (2 : ℚ) ^ ((FloatFormat.prec - 1) : ℤ) * (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) :=
        mul_lt_mul_of_pos_right hm_lt hzpos
    _ = (2 : ℚ) ^ FloatFormat.min_exp := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; ring

/-! ### Main adjacency theorem -/

/-- **Adjacency.** For positive `f` with finite `successorPos f = .finite g`,
any positive `h` (positive in the sense of `f.toVal < h.toVal`) satisfies
`g.toVal ≤ h.toVal`. Equivalently: no representable value lies strictly
between `f` and `successorPos f`. -/
theorem successorPos_le_of_toVal_lt
    (f : FiniteFp) (hs : f.s = false)
    {g : FiniteFp} (hg : successorPos f = Fp.finite g)
    (h : FiniteFp) (h_lt : (f.toVal : ℚ) < (h.toVal : ℚ)) :
    (g.toVal : ℚ) ≤ (h.toVal : ℚ) := by
  -- h is positive and nonzero
  have hf_nn : (0 : ℚ) ≤ (f.toVal : ℚ) := FiniteFp.toVal_nonneg f hs
  have hh_pos : (0 : ℚ) < (h.toVal : ℚ) := lt_of_le_of_lt hf_nn h_lt
  obtain ⟨hh_s, hh_m_pos⟩ := (FiniteFp.toVal_pos_iff (R := ℚ)).mpr hh_pos
  -- Express h_lt and target in (s = false) form
  rw [FiniteFp.toVal_pos_eq f hs, FiniteFp.toVal_pos_eq h hh_s] at h_lt
  -- Cancel the common factor 2^(f.e - prec + 1)? No, exponents differ.
  -- Branch on successorPos's case, then on h.e vs g.e.
  unfold successorPos at hg
  split_ifs at hg with hsmax hemax
  · -- Within-binade: g = ⟨false, f.e, f.m + 1, _⟩
    have h_g_eq : g = ⟨false, f.e, f.m + 1, successor_within_valid hsmax⟩ :=
      (Fp.finite.inj hg).symm
    rw [h_g_eq, FiniteFp.toVal_pos_eq _ rfl, FiniteFp.toVal_pos_eq h hh_s]
    push_cast
    rcases lt_trichotomy h.e f.e with h_he_lt | h_he_eq | h_he_gt
    · -- h.e < f.e: contradiction
      exfalso
      rcases f.valid.2.2.2 with hf_n | hf_sub
      · have hflo := two_zpow_e_le_toVal_of_normal f hs hf_n
        rw [FiniteFp.toVal_pos_eq f hs] at hflo
        have hhhi := toVal_lt_two_zpow_succ h hh_s
        rw [FiniteFp.toVal_pos_eq h hh_s] at hhhi
        have h_pow_le : (2 : ℚ) ^ (h.e + 1) ≤ (2 : ℚ) ^ f.e :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
        linarith
      · rw [hf_sub.1] at h_he_lt
        have := h.valid.1; omega
    · -- h.e = f.e: f.m < h.m ⇒ f.m + 1 ≤ h.m
      rw [h_he_eq] at h_lt ⊢
      have hzpos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
      have hmlt : (f.m : ℚ) < (h.m : ℚ) :=
        lt_of_mul_lt_mul_right h_lt (le_of_lt hzpos)
      have h1 : f.m + 1 ≤ h.m := by exact_mod_cast hmlt
      have h2 : ((f.m : ℚ) + 1) ≤ (h.m : ℚ) := by exact_mod_cast h1
      exact mul_le_mul_of_nonneg_right h2 (le_of_lt hzpos)
    · -- h.e > f.e: h normal, h.toVal ≥ 2^h.e ≥ 2^(f.e+1); g.toVal ≤ 2^(f.e+1)
      have hh_e_gt_min : FloatFormat.min_exp < h.e := by
        have := f.valid.1; omega
      have hh_n : _root_.isNormal h.m := by
        rcases h.valid.2.2.2 with hn | hsub
        · exact hn
        · exfalso; rw [hsub.1] at hh_e_gt_min; omega
      have hh_lo : (2 : ℚ) ^ h.e ≤ (h.m : ℚ) * (2 : ℚ) ^ (h.e - FloatFormat.prec + 1) := by
        have := two_zpow_e_le_toVal_of_normal h hh_s hh_n
        rwa [FiniteFp.toVal_pos_eq h hh_s] at this
      have h_e_succ_le : (2 : ℚ) ^ (f.e + 1) ≤ (2 : ℚ) ^ h.e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
      have hg_hi : ((f.m : ℚ) + 1) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
                    ≤ (2 : ℚ) ^ (f.e + 1) := by
        have hm1_le : ((f.m : ℚ) + 1) ≤ (2 : ℚ) ^ (FloatFormat.prec : ℤ) := by
          have hle : (f.m + 1 : ℕ) ≤ 2 ^ FloatFormat.prec.toNat := by omega
          have hcast : ((f.m : ℚ) + 1) ≤ (2 : ℚ) ^ FloatFormat.prec.toNat := by
            have h1 : ((f.m + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ FloatFormat.prec.toNat := by
              exact_mod_cast hle
            push_cast at h1; exact h1
          rwa [two_natPow_prec_eq_zpow (R := ℚ)] at hcast
        have hzpos : (0 : ℚ) < (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by positivity
        calc ((f.m : ℚ) + 1) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
            ≤ (2 : ℚ) ^ (FloatFormat.prec : ℤ) * (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
              mul_le_mul_of_nonneg_right hm1_le (le_of_lt hzpos)
          _ = (2 : ℚ) ^ (f.e + 1) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
              congr 1; ring
      linarith
  · -- Cross-binade: g = ⟨false, f.e + 1, 2^(prec-1), _⟩
    have h_g_eq : g = ⟨false, f.e + 1, 2^(FloatFormat.prec - 1).toNat,
        successor_cross_valid hemax⟩ := (Fp.finite.inj hg).symm
    have hsmax' : f.m + 1 = 2^FloatFormat.prec.toNat := by
      have := f.valid.2.2.1; omega
    rw [h_g_eq, FiniteFp.toVal_pos_eq _ rfl, FiniteFp.toVal_pos_eq h hh_s]
    push_cast
    rw [show (2 : ℚ) ^ (FloatFormat.prec - 1).toNat
          * (2 : ℚ) ^ (f.e + 1 - FloatFormat.prec + 1)
          = (2 : ℚ) ^ (f.e + 1) from by
        rw [two_natPow_prec_sub_one_eq_zpow (R := ℚ),
            ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; ring]
    rcases lt_trichotomy h.e (f.e + 1) with h_lt' | h_eq' | h_gt'
    · exfalso
      have hh_le : (h.m : ℚ) * (2 : ℚ) ^ (h.e - FloatFormat.prec + 1)
                    < (2 : ℚ) ^ (h.e + 1) := by
        have := toVal_lt_two_zpow_succ h hh_s
        rwa [FiniteFp.toVal_pos_eq h hh_s] at this
      have hf_n : _root_.isNormal f.m := by
        rcases f.valid.2.2.2 with hn | hsub
        · exact hn
        · exfalso
          -- f subnormal ⇒ f.m ≤ 2^(prec-1) - 1, but f.m + 1 = 2^prec > 2^(prec-1)
          have hh2 := hsub.2
          have h1 := FloatFormat.nat_two_pow_prec_sub_one_lt_two_pow_prec
          have hh3 := hsmax'
          have hpos : 0 < (2 : ℕ) ^ (FloatFormat.prec - 1).toNat := Nat.two_pow_pos _
          omega
      have hflo := two_zpow_e_le_toVal_of_normal f hs hf_n
      rw [FiniteFp.toVal_pos_eq f hs] at hflo
      rcases lt_or_eq_of_le (by omega : h.e ≤ f.e) with h_he_strict | h_he_eq
      · have h_pow_le' : (2 : ℚ) ^ (h.e + 1) ≤ (2 : ℚ) ^ f.e :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
        linarith
      · rw [← h_he_eq] at h_lt
        have hmlt' : (f.m : ℚ) < (h.m : ℚ) := by
          have hzpos : (0 : ℚ) < (2 : ℚ) ^ (h.e - FloatFormat.prec + 1) := by positivity
          exact lt_of_mul_lt_mul_right h_lt (le_of_lt hzpos)
        have hmlt'' : f.m < h.m := by exact_mod_cast hmlt'
        have hh_m_lt : h.m < 2^FloatFormat.prec.toNat := h.valid.2.2.1
        omega
    · rw [h_eq']
      have hh_n : _root_.isNormal h.m := by
        rcases h.valid.2.2.2 with hn | hsub
        · exact hn
        · exfalso; rw [hsub.1] at h_eq'; have := f.valid.1; omega
      have hh_lo := two_zpow_e_le_toVal_of_normal h hh_s hh_n
      rw [FiniteFp.toVal_pos_eq h hh_s, h_eq'] at hh_lo
      exact hh_lo
    · have hh_n : _root_.isNormal h.m := by
        rcases h.valid.2.2.2 with hn | hsub
        · exact hn
        · exfalso; rw [hsub.1] at h_gt'; have := f.valid.1; omega
      have hh_lo := two_zpow_e_le_toVal_of_normal h hh_s hh_n
      rw [FiniteFp.toVal_pos_eq h hh_s] at hh_lo
      have h_pow_le : (2 : ℚ) ^ (f.e + 1) ≤ (2 : ℚ) ^ h.e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
      linarith

/-! ## Bridge: `nextUp (Fp.finite f) = successorPos f` (positive case)

The IEEE 754 §5.3.1 `nextUp` operation, when applied to a positive finite,
agrees with the structural `successorPos`. The proof combines the upper
bound from `nextUp_finite_le_of_stepUpVal_le` and the lower bound from
adjacency. -/

/-- For positive `f`, `successorPos f` is always positively-signed (when finite). -/
private theorem successorPos_pos_sign_of_finite
    (f : FiniteFp) {g : FiniteFp} (hg : successorPos f = Fp.finite g) :
    g.s = false := by
  unfold successorPos at hg
  split_ifs at hg
  · have h_eq : g = ⟨false, f.e, f.m + 1, _⟩ := (Fp.finite.inj hg).symm
    rw [h_eq]
  · have h_eq : g = ⟨false, f.e + 1, _, _⟩ := (Fp.finite.inj hg).symm
    rw [h_eq]

/-- **Bridge to `nextUp` (positive, finite-result case).** When `successorPos f`
is finite, it equals `nextUp (Fp.finite f)`. -/
theorem nextUp_finite_eq_successorPos_of_finite
    (f : FiniteFp) (hs : f.s = false)
    {g : FiniteFp} (hg : successorPos f = Fp.finite g) :
    nextUp (Fp.finite f) = Fp.finite g := by
  -- Compute g.toVal
  have hg_val : (g.toVal : ℚ) = (f.toVal : ℚ) + (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
    successorPos_toVal_of_finite f hs hg
  -- stepUpVal f ≤ g.toVal: gap is ≥ 2^(min_exp - prec + 1) > neighborStep
  have h_step_le : stepUpVal f ≤ (g.toVal : ℚ) := by
    rw [hg_val]
    show (f.toVal : ℚ) + neighborStep ≤ (f.toVal : ℚ) + (2 : ℚ) ^ (f.e - FloatFormat.prec + 1)
    have hns_lt_min := neighborStep_lt_smallestPosSubnormal
    rw [FiniteFp.smallestPosSubnormal_toVal] at hns_lt_min
    have h_min_le : (2 : ℚ) ^ (FloatFormat.min_exp - FloatFormat.prec + 1) ≤
                    (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by have := f.valid.1; omega)
    linarith
  -- g notNegZero
  have hg_s : g.s = false := successorPos_pos_sign_of_finite f hg
  have hg_nnz : g.notNegZero := Or.inl hg_s
  -- Upper bound: nextUp (Fp.finite f) ≤ Fp.finite g
  have h_upper : nextUp (Fp.finite f) ≤ Fp.finite g :=
    nextUp_finite_le_of_stepUpVal_le f g hg_nnz h_step_le
  -- Strict lower: f < nextUp ⇒ nextUp ≠ Fp.finite f
  -- Lower bound from finite_le_nextUp; rules out NaN and -∞.
  have h_lower : Fp.finite f ≤ nextUp (Fp.finite f) := finite_le_nextUp f
  -- Match on nextUp's output (must be finite).
  match h_nu : nextUp (Fp.finite f) with
  | Fp.NaN =>
    rw [h_nu] at h_lower
    exact absurd h_lower (by simp)
  | Fp.infinite false =>
    -- +∞ ≤ Fp.finite g is impossible
    rw [h_nu] at h_upper
    exact absurd h_upper (by simp)
  | Fp.infinite true =>
    rw [h_nu] at h_lower
    -- Fp.finite f ≤ -∞ ⇒ f = NaN, but f is finite.
    rw [Fp.le_neg_inf_iff] at h_lower
    rcases h_lower with h | h <;> nomatch h
  | Fp.finite u =>
    rw [h_nu] at h_upper
    rw [Fp.finite_le_finite_iff] at h_upper
    have h_u_le_g : (u.toVal : ℚ) ≤ (g.toVal : ℚ) := FiniteFp.le_toVal_le ℚ h_upper
    have h_f_lt_u_fp : Fp.finite f < Fp.finite u := finite_lt_nextUp f u h_nu
    -- Convert to toVal lt
    have h_f_ne_u : ¬f.isZero ∨ ¬u.isZero := by
      by_cases hfz : f.isZero
      · right
        intro huz
        -- f = 0 = u: contradicts strict f < u (Fp-level).
        have h_f_eq_zero : f = 0 ∨ f = -0 := f.isZero_iff.mp hfz
        have h_u_eq_zero : u = 0 ∨ u = -0 := u.isZero_iff.mp huz
        -- Both zero (in some sign), so Fp.finite f and Fp.finite u are at most ±0.
        -- Strict Fp.finite f < Fp.finite u: must be -0 < +0. But for that f.s = true (i.e., -0).
        -- We assumed f.s = false, so f = +0, u must have higher magnitude ⇒ u not zero. Contradiction.
        have hfs0 : f = (0 : FiniteFp) := by
          rcases h_f_eq_zero with h | h
          · exact h
          · -- f = -0 means f.s = true, but hs : f.s = false. Contradiction.
            exfalso
            rw [h] at hs
            exact absurd hs (by simp [FiniteFp.neg_def, FiniteFp.zero_def])
        rw [hfs0] at h_f_lt_u_fp
        -- Fp.finite 0 < Fp.finite u with u zero (= 0 or -0) — both impossible.
        rcases h_u_eq_zero with h | h
        · rw [h] at h_f_lt_u_fp
          exact absurd h_f_lt_u_fp (lt_irrefl _)
        · rw [h] at h_f_lt_u_fp
          -- (+0 < -0) is false at FiniteFp level via the is_lt definition.
          rw [Fp.lt_def] at h_f_lt_u_fp
          simp [Fp.is_total_lt, FiniteFp.lt_def,
                FiniteFp.zero_def, FiniteFp.neg_def] at h_f_lt_u_fp
      · exact Or.inl hfz
    have h_f_lt_u_val : (f.toVal : ℚ) < (u.toVal : ℚ) :=
      FiniteFp.lt_toVal_lt ℚ h_f_lt_u_fp h_f_ne_u
    have h_g_le_u : (g.toVal : ℚ) ≤ (u.toVal : ℚ) :=
      successorPos_le_of_toVal_lt f hs hg u h_f_lt_u_val
    have h_uv_eq_gv : (u.toVal : ℚ) = (g.toVal : ℚ) := le_antisymm h_u_le_g h_g_le_u
    -- u, g positively-signed and (potentially) nonzero. u.toVal = g.toVal ⇒ u = g.
    have hu_pos : (0 : ℚ) < (u.toVal : ℚ) := by
      have hf_nn : (0 : ℚ) ≤ f.toVal := FiniteFp.toVal_nonneg f hs
      linarith
    obtain ⟨hu_s, hu_m_pos⟩ := (FiniteFp.toVal_pos_iff (R := ℚ)).mpr hu_pos
    have hu_eq_g : u = g :=
      FiniteFp.eq_of_toVal_eq' (R := ℚ) (Or.inl (by simp [FiniteFp.isZero]; omega)) h_uv_eq_gv
    rw [hu_eq_g]

/-- **Bridge to `nextUp` (positive, saturated case).** When `successorPos f`
overflows to `+∞`, `f` must be `largestFiniteFloat`, and `nextUp` agrees. -/
theorem nextUp_finite_eq_successorPos_of_saturated
    (f : FiniteFp) (hs : f.s = false)
    (hg : successorPos f = Fp.infinite false) :
    nextUp (Fp.finite f) = Fp.infinite false := by
  -- Extract f = largestFiniteFloat from hg.
  -- split_ifs auto-discharges the within-binade and cross-binade cases since
  -- their hg has form Fp.finite _ = Fp.infinite false.
  unfold successorPos at hg
  split_ifs at hg with hsmax hemax
  -- Saturated branch only: ¬hsmax ∧ ¬hemax.
  have hm_eq : f.m + 1 = 2 ^ FloatFormat.prec.toNat := by
    have := f.valid.2.2.1; omega
  have he_eq : f.e = FloatFormat.max_exp := by
    have := f.valid.2.1; omega
  have hf_eq_largest : f = FiniteFp.largestFiniteFloat := by
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨hs, he_eq, ?_⟩
    show f.m = 2^FloatFormat.prec.toNat - 1
    have hpos : 0 < (2 : ℕ) ^ FloatFormat.prec.toNat := Nat.two_pow_pos _
    omega
  rw [hf_eq_largest, nextUp_largestFiniteFloat]

/-- **Bridge to `nextUp` (positive, master form).** For positive `f`,
`nextUp (Fp.finite f) = successorPos f` — unifying both the finite-result
and saturation cases. -/
theorem nextUp_finite_eq_successorPos
    (f : FiniteFp) (hs : f.s = false) :
    nextUp (Fp.finite f) = successorPos f := by
  match h : successorPos f with
  | Fp.finite g => exact nextUp_finite_eq_successorPos_of_finite f hs h
  | Fp.infinite false => exact nextUp_finite_eq_successorPos_of_saturated f hs h
  | Fp.infinite true => exact absurd h (by
      unfold successorPos
      split_ifs <;> intro hh <;> nomatch hh)
  | Fp.NaN => exact absurd h (by
      unfold successorPos
      split_ifs <;> intro hh <;> nomatch hh)

end FiniteFp
