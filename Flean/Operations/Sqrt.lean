import Flean.Operations.RoundIntSig
import Flean.Rounding.OddInterval
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt

/-! # Floating-Point Square Root

Softfloat-style floating-point square root using `roundIntSig` as the rounding primitive.
Correctness is specialized to `ℝ` since `Real.sqrt` has no generic counterpart.
-/

section Sqrt

variable [FloatFormat]

/-- The scaling factor for square root: we left-shift before taking the integer sqrt.
Chosen so that `q = Nat.sqrt(scaled) ≥ 2^(prec+2)`, ensuring `mag > 2^(prec+3)`. -/
abbrev sqrtShift : ℕ := FloatFormat.prec.toNat + 2

/-- Compute the square root of a finite positive floating-point number. -/
def fpSqrtFinite (mode : RoundingMode) (a : FiniteFp) : Fp :=
  let e_val := a.e - FloatFormat.prec + 1
  let m' := if e_val % 2 = 0 then a.m else 2 * a.m
  let e_half := if e_val % 2 = 0 then e_val / 2 else (e_val - 1) / 2
  let scaled := m' * 2 ^ (2 * sqrtShift)
  let q := Nat.sqrt scaled
  let rem := scaled - q * q
  let mag := 2 * q + (if rem = 0 then 0 else 1)
  let e_base := e_half - (sqrtShift : ℤ) - 1
  roundIntSig mode false mag e_base

/-- IEEE 754 floating-point square root with full special-case handling. -/
def fpSqrt (mode : RoundingMode) (x : Fp) : Fp :=
  match x with
  | .NaN => .NaN
  | .infinite true => .NaN
  | .infinite false => .infinite false
  | .finite a =>
    if a.m = 0 then
      Fp.finite ⟨a.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
    else if a.s then .NaN
    else fpSqrtFinite mode a

/-! ## Helper lemmas -/

private lemma sqrt_two_zpow_sq (k : ℤ) :
    Real.sqrt ((2 : ℝ) ^ (2 * k)) = (2 : ℝ) ^ k := by
  conv_lhs => rw [show (2 : ℤ) * k = k * 2 from by ring]
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
  exact Real.sqrt_sq (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)

/-! ## Full Correctness -/

set_option maxHeartbeats 800000 in
/-- `fpSqrtFinite` correctly rounds the exact square root for all rounding modes. -/
theorem fpSqrtFinite_correct (mode : RoundingMode) (a : FiniteFp)
    (ha_pos : a.s = false) (ha_nz : a.m ≠ 0) :
    fpSqrtFinite mode a = mode.round (Real.sqrt (a.toVal : ℝ)) := by
  -- Set up variables matching fpSqrtFinite's body
  set e_val := a.e - FloatFormat.prec + 1 with he_val_def
  set m' := (if e_val % 2 = 0 then a.m else 2 * a.m) with hm'_def
  set e_half := (if e_val % 2 = 0 then e_val / 2 else (e_val - 1) / 2) with he_half_def
  set scaled := m' * 2 ^ (2 * sqrtShift) with hscaled_def
  set q := Nat.sqrt scaled with hq_def
  set rem := scaled - q * q with hrem_def
  set e_base := e_half - (sqrtShift : ℤ) - 1 with he_base_def
  -- Basic positivity facts
  have hm'_pos : 0 < m' := by simp only [hm'_def]; split_ifs <;> omega
  have hscaled_pos : 0 < scaled := by positivity
  have hq_pos : 0 < q := Nat.sqrt_pos.mpr hscaled_pos
  -- Bridge: a.toVal = m' * 2^(2*e_half) as reals
  have h_toVal : (a.toVal : ℝ) = (m' : ℝ) * (2 : ℝ) ^ (2 * e_half) := by
    have hs : (FiniteFp.sign' a : ℝ) = 1 := by
      simp [FiniteFp.sign', ha_pos]
    unfold FiniteFp.toVal; rw [FloatFormat.radix_val_eq_two, hs, one_mul]
    -- Goal: ↑a.m * (2:ℝ)^e_val = ↑m' * (2:ℝ)^(2*e_half)
    by_cases h : e_val % 2 = 0
    · rw [show m' = a.m from if_pos h, show e_half = e_val / 2 from if_pos h]
      congr 1; congr 1
      have := Int.ediv_add_emod e_val 2; omega
    · rw [show m' = 2 * a.m from if_neg h, show e_half = (e_val - 1) / 2 from if_neg h]
      rw [show (↑(2 * a.m) : ℝ) = 2 * (↑a.m : ℝ) from by push_cast; ring]
      have heval : e_val = 2 * ((e_val - 1) / 2) + 1 := by
        have := Int.ediv_add_emod (e_val - 1) 2; omega
      rw [show a.e - FloatFormat.prec + 1 = 2 * ((e_val - 1) / 2) + 1 from
        he_val_def ▸ heval]
      norm_num
      rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]; ring
  -- Bridge: scaled cast to ℝ
  have h_scaled_cast : (scaled : ℝ) = (m' : ℝ) * (2 : ℝ) ^ (2 * (sqrtShift : ℤ)) := by
    have : scaled = m' * 2 ^ (2 * sqrtShift) := rfl
    rw [this]; push_cast
    rw [← zpow_natCast (2 : ℝ) (2 * sqrtShift)]; congr 1
  -- Bridge: √(a.toVal) = √(scaled) * 2^(e_half - sqrtShift)
  have hbridge : Real.sqrt (a.toVal : ℝ) =
      Real.sqrt (scaled : ℝ) * (2 : ℝ) ^ (e_half - (sqrtShift : ℤ)) := by
    rw [h_toVal, h_scaled_cast,
        Real.sqrt_mul (Nat.cast_nonneg m') ((2 : ℝ) ^ (2 * e_half)),
        Real.sqrt_mul (Nat.cast_nonneg m') ((2 : ℝ) ^ (2 * (sqrtShift : ℤ))),
        sqrt_two_zpow_sq e_half, sqrt_two_zpow_sq (sqrtShift : ℤ),
        mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; congr 1; omega
  -- Key exponent: 2^(e_half - sqrtShift) = 2 * E where E = 2^e_base
  set E := (2 : ℝ) ^ e_base with hE_def
  have hE_pos : (0 : ℝ) < E := zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have hexp_split : (2 : ℝ) ^ (e_half - (sqrtShift : ℤ)) = 2 * E := by
    rw [hE_def, show e_half - (sqrtShift : ℤ) = e_base + 1 from by omega,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
  -- Nat.sqrt bounds
  have hq_sq_le : q * q ≤ scaled := Nat.sqrt_le scaled
  have hlt_succ_sq : scaled < (q + 1) * (q + 1) := by rw [hq_def]; exact Nat.lt_succ_sqrt scaled
  -- Unfold fpSqrtFinite to roundIntSig
  have hfp_unfold : fpSqrtFinite mode a =
      roundIntSig mode false (2 * q + (if rem = 0 then 0 else 1)) e_base := by
    unfold fpSqrtFinite
    simp only [← he_val_def, ← hm'_def, ← he_half_def, ← hscaled_def,
               ← hq_def, ← hrem_def, ← he_base_def]
  -- Case split: exact (rem = 0) vs sticky (rem ≠ 0)
  by_cases hrem : rem = 0
  · -- === Exact case: rem = 0, mag = 2*q ===
    have hscaled_eq : scaled = q * q := by omega
    have hmag_ne : 2 * q ≠ 0 := by omega
    -- √(scaled) = q
    have hsqrt_scaled : Real.sqrt (scaled : ℝ) = (q : ℝ) := by
      rw [show (scaled : ℝ) = (q : ℝ) * (q : ℝ) from by exact_mod_cast hscaled_eq]
      exact Real.sqrt_mul_self (by positivity)
    -- intSigVal false (2*q) e_base = √(a.toVal)
    have h_isv : intSigVal (R := ℝ) false (2 * q) e_base = Real.sqrt (a.toVal : ℝ) := by
      rw [hbridge, hsqrt_scaled]
      show (↑(2 * q) : ℝ) * (2 : ℝ) ^ e_base = (q : ℝ) * (2 : ℝ) ^ (e_half - (sqrtShift : ℤ))
      rw [show (↑(2 * q) : ℝ) = 2 * (q : ℝ) from by push_cast; ring]
      rw [hexp_split]; ring
    rw [hfp_unfold, if_pos hrem, show 2 * q + 0 = 2 * q from by omega,
        roundIntSig_correct (R := ℝ) mode _ _ _ hmag_ne, h_isv]
  · -- === Sticky case: rem ≠ 0, mag = 2*q + 1 (odd) ===
    have hmag_ne : 2 * q + 1 ≠ 0 := by omega
    rw [hfp_unfold, if_neg hrem,
        roundIntSig_correct (R := ℝ) mode _ _ _ hmag_ne]
    -- Set up sticky value and mag
    set mag := 2 * q + 1 with hmag_def
    -- mag is odd
    have hmag_odd : mag % 2 = 1 := by omega
    -- q ≥ 2^(prec+2)
    have hq_lower : 2 ^ (FloatFormat.prec.toNat + 2) ≤ q := by
      rw [hq_def]
      have h_scaled_ge : 2 ^ (2 * sqrtShift) ≤ scaled := by
        rw [hscaled_def]; exact Nat.le_mul_of_pos_left _ hm'_pos
      have h_sq : 2 ^ sqrtShift * 2 ^ sqrtShift = 2 ^ (2 * sqrtShift) := by
        rw [← Nat.pow_add]; ring_nf
      calc 2 ^ (FloatFormat.prec.toNat + 2)
          = 2 ^ sqrtShift := rfl
        _ = Nat.sqrt (2 ^ sqrtShift * 2 ^ sqrtShift) := (Nat.sqrt_eq _).symm
        _ = Nat.sqrt (2 ^ (2 * sqrtShift)) := by rw [h_sq]
        _ ≤ Nat.sqrt scaled := Nat.sqrt_le_sqrt h_scaled_ge
    -- mag > 2^(prec+3)
    have hmag_large : 2 ^ (FloatFormat.prec.toNat + 3) < mag := by
      have : 2 ^ (FloatFormat.prec.toNat + 3) = 2 * 2 ^ (FloatFormat.prec.toNat + 2) := by
        rw [Nat.pow_succ]; ring
      omega
    -- Sticky value is in interval
    have abs_sticky := (mag : ℝ) * E
    have hs_lo : ((mag : ℤ) - 1 : ℝ) * E < (mag : ℝ) * E := by
      apply mul_lt_mul_of_pos_right _ hE_pos
      exact_mod_cast (show (mag : ℤ) - 1 < mag from by omega)
    have hs_hi : (mag : ℝ) * E < ((mag : ℤ) + 1 : ℝ) * E := by
      apply mul_lt_mul_of_pos_right _ hE_pos
      exact_mod_cast (show (mag : ℤ) < mag + 1 from by omega)
    -- √(scaled) bounds: q < √(scaled) < q + 1 (strict since rem ≠ 0)
    have hq_sq_lt : q * q < scaled := by omega
    have hsqrt_gt : (q : ℝ) < Real.sqrt (scaled : ℝ) := by
      rw [show (q : ℝ) = Real.sqrt ((q : ℝ) ^ 2) from
        (Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (q : ℝ))).symm]
      apply Real.sqrt_lt_sqrt (by positivity)
      rw [sq]; exact_mod_cast hq_sq_lt
    have hsqrt_lt : Real.sqrt (scaled : ℝ) < (q : ℝ) + 1 := by
      rw [show (q : ℝ) + 1 = Real.sqrt (((q : ℝ) + 1) ^ 2) from
        (Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)).symm]
      apply Real.sqrt_lt_sqrt (by positivity)
      rw [sq]; exact_mod_cast hlt_succ_sq
    -- Exact value in interval: (mag-1)*E < √(a.toVal) < (mag+1)*E
    have he_lo : ((mag : ℤ) - 1 : ℝ) * E < Real.sqrt (a.toVal : ℝ) := by
      rw [hbridge, hexp_split]
      have : ((mag : ℤ) - 1 : ℝ) = 2 * (q : ℝ) := by rw [hmag_def]; push_cast; ring
      rw [this]
      calc 2 * (q : ℝ) * E = (q : ℝ) * (2 * E) := by ring
        _ < Real.sqrt ↑scaled * (2 * E) :=
            mul_lt_mul_of_pos_right hsqrt_gt (by linarith)
    have he_hi : Real.sqrt (a.toVal : ℝ) < ((mag : ℤ) + 1 : ℝ) * E := by
      rw [hbridge, hexp_split]
      have : ((mag : ℤ) + 1 : ℝ) = 2 * ((q : ℝ) + 1) := by rw [hmag_def]; push_cast; ring
      rw [this]
      calc Real.sqrt ↑scaled * (2 * E)
          < ((q : ℝ) + 1) * (2 * E) :=
            mul_lt_mul_of_pos_right hsqrt_lt (by linarith)
        _ = 2 * ((q : ℝ) + 1) * E := by ring
    -- Apply round_eq_on_odd_interval
    have hround_eq := round_eq_on_odd_interval (R := ℝ) mode hmag_odd hmag_large
      hs_lo hs_hi he_lo he_hi
    -- Connect intSigVal to mag * E
    have h_isv : intSigVal (R := ℝ) false mag e_base = (mag : ℝ) * E := by
      unfold intSigVal; simp [hE_def]
    rw [h_isv, hround_eq]

end Sqrt
