import Flean.IntegerEquivalence.UlpPow2

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
