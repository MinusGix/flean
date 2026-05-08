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

end FiniteFp
