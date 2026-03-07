import Flean.Operations.StickyExtract
import Flean.Linearize.Linearize
import Flean.BoundCalc.BoundCalc

/-! # Shared termination infrastructure for sticky cell extraction

Generic lemmas and definitions shared between operation-specific termination proofs
(e.g., `ExpTermination.lean`, `LogTermination.lean`).

## Contents

### Shared constants
- `baseTaylorTerms`: base number of Taylor terms (`prec + 10`)
- `stickyFuel`: generic fuel formula, quadratic in input size

### Generic lemmas
- `int_log_le_nat_log2_diff`: `Int.log 2 r ≤ Nat.log2(r.num) - Nat.log2(r.den)` for positive rational `r`
- `stickyShift_le_of_int_log`: `stickyShift r ≤ prec + 4 - Int.log 2 r` for positive `r`
- `two_pow_mul_half_pow`: `2^a · (1/2)^(a+b) = (1/2)^b`
- `err1_factorial_bound`: Taylor remainder factorial decay bound

### Tight bracket lemma
- `stickyTryOne_of_tight_bracket`: when bracket width · 2^s < gap δ, `stickyTryOne` succeeds
-/

section StickyTermination

variable [FloatFormat]

/-! ## Shared constants -/

/-- Base number of Taylor terms for sticky extraction. Both exp and log use `prec + 10`
as the starting point, with `iter * 10` additional terms per iteration. -/
def baseTaylorTerms : ℕ := FloatFormat.prec.toNat + 10

/-- Generic fuel formula for sticky extraction, quadratic in input size.
Both `expFuel` and `logFuel` use this same formula applied to their inputs.

The quadratic term `a² / b` accommodates Padé/irrationality measure convergence.
Linear terms cover the shift, ln2 precision, and base Taylor order.
The `log₂` factor ensures fuel grows faster than the effective threshold. -/
def stickyFuel (x : ℚ) : ℕ :=
  let ab := x.num.natAbs ^ 2 / x.den + x.num.natAbs + x.den + FloatFormat.prec.toNat + 100
  15 * ab * (Nat.log2 ab + 1) + 200

/-! ## Generic lemmas -/

omit [FloatFormat] in
/-- For a positive rational, `Int.log 2 r ≤ Nat.log2 r.num.natAbs - Nat.log2 r.den`.
This follows from `r < 2^(Nat.log2 p + 1) / 2^(Nat.log2 d) = 2^(lp - ld + 1)`. -/
lemma int_log_le_nat_log2_diff (r : ℚ) (hr : 0 < r) :
    Int.log 2 r ≤ (Nat.log2 r.num.natAbs : ℤ) - (Nat.log2 r.den : ℤ) := by
  set p := r.num.natAbs
  set d := r.den
  set lp := Nat.log2 p
  set ld := Nat.log2 d
  have hp_pos : 0 < p := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hr))
  have hp_ne : p ≠ 0 := by omega
  have hd_pos : (0 : ℚ) < (d : ℚ) := Nat.cast_pos.mpr r.den_pos
  have hd_ne : d ≠ 0 := ne_of_gt r.den_pos
  have hplt : p < 2 ^ (lp + 1) := (Nat.log2_lt hp_ne).mp (Nat.lt_succ_of_le (le_refl lp))
  have hdle : (2 : ℚ) ^ (ld : ℤ) ≤ (d : ℚ) := by
    rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le hd_ne
  suffices r < (2 : ℚ) ^ ((lp : ℤ) - (ld : ℤ) + 1) by
    have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hr).mp this
    omega
  have hr_eq : r = (p : ℚ) / (d : ℚ) := by
    have hnum_pos := Rat.num_pos.mpr hr
    have hnum : (r.num : ℚ) = ((p : ℕ) : ℤ) := by
      simp [p, Int.natAbs_of_nonneg (le_of_lt hnum_pos)]
    rw [show (p : ℚ) / (d : ℚ) = ((p : ℕ) : ℤ) / ((d : ℕ) : ℤ) from by push_cast; ring]
    rw [← hnum]; exact (Rat.num_div_den r).symm
  have h2ld_pos : (0 : ℚ) < (2 : ℚ) ^ (ld : ℤ) := by positivity
  calc r = (p : ℚ) / (d : ℚ) := hr_eq
    _ ≤ (p : ℚ) / (2 : ℚ) ^ (ld : ℤ) := by
        rw [div_le_div_iff₀ hd_pos h2ld_pos]
        exact mul_le_mul_of_nonneg_left hdle (by exact_mod_cast hp_pos.le)
    _ < (2 : ℚ) ^ ((lp + 1 : ℕ) : ℤ) / (2 : ℚ) ^ (ld : ℤ) := by
        rw [div_lt_div_iff₀ h2ld_pos h2ld_pos, zpow_natCast]
        exact_mod_cast Nat.mul_lt_mul_of_pos_right hplt (by positivity : 0 < 2 ^ ld)
    _ = (2 : ℚ) ^ ((lp : ℤ) - (ld : ℤ) + 1) := by
        rw [show ((lp + 1 : ℕ) : ℤ) = (lp : ℤ) + 1 from by omega,
          show (lp : ℤ) + 1 = ((lp : ℤ) - (ld : ℤ) + 1) + (ld : ℤ) from by omega,
          zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast,
          mul_div_cancel_right₀ _ (by positivity : (2 : ℚ) ^ ld ≠ 0)]

/-- The shift `stickyShift r` for a positive rational is bounded by `prec + 4 - Int.log 2 r`. -/
lemma stickyShift_le_of_int_log (r : ℚ) (hr : 0 < r) :
    stickyShift r ≤ ((FloatFormat.prec.toNat : ℤ) + 4 - Int.log 2 r).toNat := by
  simp only [stickyShift]
  have h := int_log_le_nat_log2_diff r hr
  exact Int.toNat_le_toNat (by omega)

-- Helper: 2^a * (1/2)^(a+b) = (1/2)^b
omit [FloatFormat] in
lemma two_pow_mul_half_pow (a b : ℕ) :
    (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
  rw [one_div_pow, one_div_pow, pow_add]
  field_simp

-- Helper: err₁ bound from factorial geometric decay
omit [FloatFormat] in
/-- Taylor remainder error bound: `2^(N+2)·(N+2)/((N+1)!·(N+1)) ≤ (8/3)·(1/2)^(N-4)` for `N ≥ 4`.
This is the factorial decay that drives termination. -/
lemma err1_factorial_bound (N : ℕ) (hN : 4 ≤ N) :
    (2:ℝ)^(N+2) * (N+2:ℝ) / ((N+1).factorial * (N+1:ℝ)) ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := by
  have hfac_pos : (0:ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h_fac : (2:ℝ)^N / ↑N.factorial ≤
      (2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4) := by
    have := pow_div_factorial_geometric_bound 2 (by norm_num) 2 (by norm_num) N (by omega)
    simpa using this
  have h_init : (2:ℝ)^4 / ↑(4:ℕ).factorial = 2/3 := by norm_num [Nat.factorial]
  have h2N2 : (2:ℝ)^(N+2) = 4 * (2:ℝ)^N := by rw [pow_add]; ring
  have hfac_succ : ((N+1).factorial : ℝ) = (N+1:ℝ) * N.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hN_r : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN2_le : (N+2:ℝ) ≤ (N+1:ℝ) * (N+1:ℝ) := by nlinarith
  rw [h2N2, hfac_succ]
  have h2N_pos : (0:ℝ) < (2:ℝ)^N := by positivity
  have herr1_aux : 4 * (2:ℝ)^N * (N+2:ℝ) / ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ)) ≤
      4 * (2:ℝ)^N / ↑N.factorial := by
    have h_cancel : (0:ℝ) < 4 * (2:ℝ)^N * ↑N.factorial := by positivity
    rw [div_le_div_iff₀ (by positivity) hfac_pos]
    have : 4 * (2:ℝ)^N * (N+2:ℝ) * ↑N.factorial =
        4 * (2:ℝ)^N * ↑N.factorial * (N+2:ℝ) := by ring
    have : 4 * (2:ℝ)^N * ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ)) =
        4 * (2:ℝ)^N * ↑N.factorial * ((N+1:ℝ) * (N+1:ℝ)) := by ring
    nlinarith
  have h4_fac : 4 * (2:ℝ)^N / ↑N.factorial ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := by
    have : 4 * ((2:ℝ)^N / ↑N.factorial) ≤ 4 * ((2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4)) :=
      by bound_calc
    calc 4 * (2:ℝ)^N / ↑N.factorial
        = 4 * ((2:ℝ)^N / ↑N.factorial) := by ring
      _ ≤ 4 * ((2:ℝ)^4 / ↑(4:ℕ).factorial * (1/2:ℝ)^(N-4)) := this
      _ = (8/3:ℝ) * (1/2:ℝ)^(N-4) := by rw [h_init]; ring
  calc 4 * (2:ℝ)^N * (N+2:ℝ) / ((N+1:ℝ) * ↑N.factorial * (N+1:ℝ))
      ≤ 4 * (2:ℝ)^N / ↑N.factorial := herr1_aux
    _ ≤ (8/3:ℝ) * (1/2:ℝ)^(N-4) := h4_fac

/-! ## Generic tight bracket lemma

When the bracket width multiplied by `2^s` is less than the irrationality gap `δ`,
the floors of `lower · 2^s` and `upper · 2^s` agree, so `stickyTryOne` succeeds. -/

/-- When bracket width · 2^s < δ and v stays δ-away from all integers shifted by 2^s,
the nat-div floors agree and `stickyTryOne` succeeds.

This is the generic meeting point between width bounds and gap bounds. -/
theorem stickyTryOne_of_tight_bracket
    (bounds : ℕ → ℚ × ℚ) (iter : ℕ) (v : ℝ)
    (hlower_pos : 0 < (bounds iter).1)
    (hlower_lt_v : ((bounds iter).1 : ℝ) < v)
    (hv_le_upper : v ≤ ((bounds iter).2 : ℝ))
    (δ : ℝ)
    (hδ_gap : ∀ m : ℤ, |v * 2 ^ (stickyShift (bounds iter).1) - (m : ℝ)| ≥ δ)
    (hwidth : (((bounds iter).2 : ℝ) - ((bounds iter).1 : ℝ)) *
      2 ^ (stickyShift (bounds iter).1) < δ) :
    (stickyTryOne bounds iter).isSome = true := by
  set lower := (bounds iter).1
  set upper := (bounds iter).2
  set s := stickyShift lower
  set q_lo := lower.num.natAbs * 2 ^ s / lower.den
  set q_hi := upper.num.natAbs * 2 ^ s / upper.den
  have hu_pos : 0 < upper :=
    lt_trans hlower_pos (by exact_mod_cast (lt_of_lt_of_le hlower_lt_v hv_le_upper : (lower : ℝ) < upper))
  have h2s_pos : (0 : ℝ) < 2 ^ s := by positivity
  -- Gap argument: no integer in (lower·2^s, upper·2^s]
  have h_no_int : ∀ m : ℤ,
      ¬((lower : ℝ) * 2 ^ s < (m : ℝ) ∧ (m : ℝ) ≤ (upper : ℝ) * 2 ^ s) := by
    intro m ⟨hm_lo, hm_hi⟩
    have : |v * 2 ^ s - (m : ℝ)| < δ := by
      rw [abs_lt]; constructor <;>
      nlinarith [mul_lt_mul_of_pos_right hlower_lt_v h2s_pos,
                 mul_le_mul_of_nonneg_right hv_le_upper h2s_pos.le, hwidth]
    linarith [hδ_gap m]
  -- By contradiction: if q_lo ≠ q_hi, find integer m = q_lo + 1 in the gap
  have hq : q_lo = q_hi := by
    by_contra hne
    have hle : q_lo ≤ q_hi := by
      suffices h : (q_lo : ℝ) < (q_hi : ℝ) + 1 by
        have : q_lo < q_hi + 1 := by exact_mod_cast h
        omega
      calc (q_lo : ℝ) ≤ (lower : ℝ) * 2 ^ s := by
              rw [Rat.cast_eq_natAbs_div_den lower hlower_pos, div_mul_eq_mul_div,
                le_div_iff₀ (Nat.cast_pos.mpr lower.den_pos)]
              exact_mod_cast nat_floor_div_mul_le lower.num.natAbs lower.den s
        _ ≤ (upper : ℝ) * 2 ^ s := by
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast le_of_lt (lt_of_lt_of_le hlower_lt_v hv_le_upper))
                h2s_pos.le
        _ < (q_hi : ℝ) + 1 := by
              rw [Rat.cast_eq_natAbs_div_den upper hu_pos, div_mul_eq_mul_div,
                div_lt_iff₀ (Nat.cast_pos.mpr upper.den_pos)]
              rw [show (↑q_hi + (1 : ℝ)) * ↑upper.den = ((q_hi + 1 : ℕ) : ℝ) * ↑upper.den
                from by push_cast; ring]
              exact_mod_cast real_lt_nat_floor_div_succ_mul
                upper.num.natAbs upper.den s upper.den_pos
    have hlt : q_lo < q_hi := lt_of_le_of_ne hle hne
    have hm_lo : (lower : ℝ) * 2 ^ s < ((q_lo + 1 : ℕ) : ℝ) := by
      rw [Rat.cast_eq_natAbs_div_den lower hlower_pos, div_mul_eq_mul_div,
        div_lt_iff₀ (Nat.cast_pos.mpr lower.den_pos)]
      exact real_lt_nat_floor_div_succ_mul lower.num.natAbs lower.den s lower.den_pos
    have hm_hi : ((q_lo + 1 : ℕ) : ℝ) ≤ (upper : ℝ) * 2 ^ s := by
      rw [Rat.cast_eq_natAbs_div_den upper hu_pos, div_mul_eq_mul_div,
        le_div_iff₀ (Nat.cast_pos.mpr upper.den_pos)]
      calc ((q_lo + 1 : ℕ) : ℝ) * ↑upper.den
          ≤ (q_hi : ℝ) * ↑upper.den := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) (Nat.cast_nonneg _)
        _ ≤ (upper.num.natAbs : ℝ) * 2 ^ s :=
            nat_floor_div_mul_le upper.num.natAbs upper.den s
    exact h_no_int (q_lo + 1 : ℕ) ⟨by exact_mod_cast hm_lo, by exact_mod_cast hm_hi⟩
  -- Conclude stickyTryOne returns some
  simp only [stickyTryOne]
  split_ifs with h
  · rfl
  · exact absurd hq h

/-! ## Uniform gap from pointwise gap

When each shift value `s` has its own irrationality gap `δ_s > 0` with `1/δ_s ≤ 2^{L_s}`
and all `L_s` share a common upper bound, we can take the minimum over `s ≤ T` to get
a single uniform `δ` that works for all shifts simultaneously. -/

omit [FloatFormat] in
/-- Combine pointwise irrationality gaps into a uniform gap over bounded shifts.
Given `gap_at s` producing `(δ, L)` for each `s`, returns a single `(δ, L)` for all `s ≤ T`. -/
theorem uniform_gap_from_pointwise (T L_bound : ℕ)
    (gap : ℕ → ℤ → ℝ)
    (gap_at : ∀ s ≤ T, ∃ δ > 0, ∃ L : ℕ, L ≤ L_bound ∧
      (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧ ∀ m : ℤ, gap s m ≥ δ) :
    ∃ δ > 0, ∃ L : ℕ, L ≤ L_bound ∧
    (1 : ℝ) / δ ≤ (2 : ℝ) ^ L ∧ ∀ s ≤ T, ∀ m : ℤ, gap s m ≥ δ := by
  induction T with
  | zero =>
    obtain ⟨δ, hδ, L, hL, hLd, hg⟩ := gap_at 0 (by omega)
    exact ⟨δ, hδ, L, hL, hLd, fun s hs m => by interval_cases s; exact hg m⟩
  | succ n ih =>
    obtain ⟨δ₁, hδ₁, L₁, hL₁, hL₁d, hδ₁g⟩ := ih (fun s hs => gap_at s (by omega))
    obtain ⟨δ₂, hδ₂, L₂, hL₂, hL₂d, hδ₂g⟩ := gap_at (n + 1) (by omega)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max L₁ L₂, max_le hL₁ hL₂, ?_, fun s hs m => ?_⟩
    · rcases le_total δ₁ δ₂ with h | h
      · rw [min_eq_left h]
        exact le_trans hL₁d (by linearize)
      · rw [min_eq_right h]
        exact le_trans hL₂d (by linearize)
    · rcases Nat.eq_or_lt_of_le hs with rfl | hlt
      · exact le_trans (min_le_right _ _) (hδ₂g m)
      · exact le_trans (min_le_left _ _) (hδ₁g s (by omega) m)

end StickyTermination
