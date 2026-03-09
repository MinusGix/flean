import Flean.Operations.Fast2Sum
import Flean.Operations.MulPow2
import Flean.Rounding.GridInstance

/-! # Veltkamp Splitting

Veltkamp splitting (Dekker 1971) decomposes a floating-point number `a` into two
non-overlapping parts `a_hi + a_lo = a` exactly, where `a_hi` has at most `s`
significant bits. This is the key building block for TwoProduct without FMA.

## Algorithm

Given a splitting parameter `s` with `1 ≤ s ≤ p - 1`:
```
C    = 2^s + 1           -- splitting constant (representable since s+1 ≤ p)
γ    = fl(C * a)          -- multiply by splitting constant
δ    = fl(a - γ)          -- residual
a_hi = fl(γ + δ)          -- high part
a_lo = fl(a - a_hi)       -- low part
```

## Proof Strategy

The proof uses **grid alignment** via `RModeGrid`:
1. All values `a`, `γ`, `δ`, `a_hi` lie on the same grid `2^g` where `g = e_a - p + 1`
2. The difference `a - a_hi` is on this grid with bounded integer coefficient
3. Therefore `a - a_hi` is representable, making the final subtraction exact
4. Conclude `a_hi + a_lo = a`
-/

section VeltkampSplit

variable [FloatFormat]
local notation "prec" => FloatFormat.prec
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## Helper: extracting toVal from Fp equality -/

private theorem toVal_of_fp_eq (x y : FiniteFp) (h : (x : Fp) = (y : Fp)) :
    x.toVal (R := R) = y.toVal := by
  have := Fp.finite.inj h; subst this; rfl

/-! ## Helper: addition of zero-summing floats -/

private theorem fpAddFinite_zero_of_eq_sum [RModeExec] (a b : FiniteFp)
    (hsum : (a.toVal : R) + b.toVal = 0) :
    ∃ f : FiniteFp, a + b = f ∧ f.toVal (R := R) = 0 := by
  have hexact := fpAddFinite_exact_sum R a b
  set isum := addAlignedSumInt a b
  set e_base := min a.e b.e - prec + 1
  have hisum_zero : (isum : R) = 0 := by
    have h2ne : (2 : R) ^ e_base ≠ 0 := zpow_ne_zero _ (by norm_num)
    have : (isum : R) * (2 : R) ^ e_base = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right h2ne
  have hisum_int_zero : isum = 0 := by exact_mod_cast hisum_zero
  have hkey : condNeg a.s (a.m : ℤ) * 2 ^ (a.e - min a.e b.e).toNat +
      condNeg b.s (b.m : ℤ) * 2 ^ (b.e - min a.e b.e).toNat = 0 := hisum_int_zero
  let fz : FiniteFp := ⟨exactCancelSign a.s b.s, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  refine ⟨fz, ?_, FiniteFp.toVal_isZero rfl⟩
  simp [fpAddFinite, hkey, fz, exactCancelSign]

/-! ## Grid rounding error bound

For nearest rounding of `n * 2^g` to `n' * 2^g`, the integer coefficient error
`|n - n'|` is bounded by `2^(M - prec - 1)` when `|n| < 2^M`. -/

/-- ULP/2 bound for nearest rounding, extended to handle negative values
via `RModeConj.round_neg` and deriving overflow-freedom from `round(x) = finite f`. -/
private theorem nearest_abs_error_le_ulp_half_signed
    [RMode R] [RModeNearest R] [RModeConj R]
    (x : R) (hx_ne : x ≠ 0) (hx_norm : (2 : R) ^ FloatFormat.min_exp ≤ |x|)
    (f : FiniteFp) (hf : ○x = Fp.finite f) :
    |x - (f.toVal : R)| ≤ Fp.ulp x / 2 := by
  -- Derive x < overflowThreshold from round(x) = finite f
  have hx_lt_ot : |x| < FloatFormat.overflowThreshold R := by
    by_contra h; push_neg at h
    rcases le_or_gt x 0 with hneg | hpos
    · have hlt : x < 0 := lt_of_le_of_ne hneg hx_ne
      have : -x > 0 := neg_pos.mpr hlt
      have h_neg_ge : FloatFormat.overflowThreshold R ≤ -x := by
        rwa [abs_of_neg hlt] at h
      have := RModeNearest.overflow_pos_inf (-x) h_neg_ge
      have hconj := RModeConj.round_neg x (ne_of_lt hlt)
      rw [hf, Fp.neg_finite] at hconj
      rw [hconj] at this; cases this
    · have h_ge : FloatFormat.overflowThreshold R ≤ x := by
        rwa [abs_of_pos hpos] at h
      have := RModeNearest.overflow_pos_inf x h_ge
      rw [this] at hf; cases hf
  have hx_lt_max : |x| < (2 : R) ^ (FloatFormat.max_exp + 1) :=
    lt_trans hx_lt_ot FloatFormat.overflowThreshold_lt_zpow_max_exp_succ
  rcases le_or_gt x 0 with hneg | hpos
  · -- x < 0
    have hlt : x < 0 := lt_of_le_of_ne hneg hx_ne
    have hNR : isNormalRange (-x) := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_neg hlt] at hx_norm
      · rwa [abs_of_neg hlt] at hx_lt_max
    have hconj : ○(-x) = Fp.finite (-f) := by
      rw [RModeConj.round_neg x (ne_of_lt hlt), hf, Fp.neg_finite]
    have h := RModeNearest_abs_error_le_ulp_half (-x) hNR (-f) hconj
    rw [FiniteFp.toVal_neg_eq_neg, neg_sub_neg, abs_sub_comm, Fp.ulp_eq_neg] at h
    exact h
  · -- x > 0
    have hNR : isNormalRange x := by
      refine ⟨?_, ?_⟩
      · rwa [abs_of_pos hpos] at hx_norm
      · rwa [abs_of_pos hpos] at hx_lt_max
    exact RModeNearest_abs_error_le_ulp_half x hNR f hf

/-- Grid coefficient rounding error for nearest mode.
If `round(n * 2^g) = f` with `f.toVal = n' * 2^g` and `n.natAbs < 2^M`
where `M ≥ prec + 1`, then `(n - n').natAbs ≤ 2^(M - prec - 1)`.

The proof uses `nearest_abs_error_le_ulp_half_signed` for the normal case
and shows exact rounding for the subnormal case (via idempotence). -/
private theorem nearest_grid_coeff_error
    [RMode R] [RModeNearest R] [RModeConj R]
    (n : ℤ) (g : ℤ) (f : FiniteFp) (n' : ℤ) (M : ℕ)
    (hg_ge : g ≥ FloatFormat.min_exp - prec + 1)
    (hg_le : g + prec - 1 ≤ FloatFormat.max_exp)
    (hn_ne : n ≠ 0)
    (hn_bound : n.natAbs < 2 ^ M)
    (hM_ge : precNat + 1 ≤ M)
    (hround : ○((n : R) * (2 : R) ^ g) = Fp.finite f)
    (hfg : f.toVal (R := R) = (n' : R) * (2 : R) ^ g) :
    (n - n').natAbs ≤ 2 ^ (M - precNat - 1) := by
  set x := (n : R) * (2 : R) ^ g with x_def
  have h2_ne : (2 : R) ≠ 0 := by norm_num
  have h2g_ne : (2 : R) ^ g ≠ 0 := zpow_ne_zero _ h2_ne
  have h2g_pos : (0 : R) < (2 : R) ^ g := by positivity
  have hx_ne : x ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn_ne) h2g_ne
  -- The error in terms of grid coefficients
  have hdiff : x - f.toVal (R := R) = ((n - n' : ℤ) : R) * (2 : R) ^ g := by
    rw [x_def, hfg]; push_cast; ring
  -- |n| < 2^M in R
  have hn_abs_R : |(n : R)| < (2 : R) ^ (M : ℤ) := by
    have h_int : |n| < (2 : ℤ) ^ M := by
      calc |n| = ↑n.natAbs := (Int.natCast_natAbs n).symm
        _ < ↑(2 ^ M : ℕ) := by exact_mod_cast hn_bound
        _ = (2 : ℤ) ^ M := by push_cast; ring
    rw [← Int.cast_abs, zpow_natCast]; push_cast; exact_mod_cast h_int
  -- |x| < 2^(M + g) = 2^M * 2^g
  have hx_abs_bound : |x| < (2 : R) ^ ((M : ℤ) + g) := by
    rw [x_def, abs_mul, abs_of_pos h2g_pos, zpow_add₀ h2_ne]
    exact mul_lt_mul_of_pos_right hn_abs_R h2g_pos
  -- Case split on |x| ≥ 2^min_exp (normal vs subnormal)
  by_cases hnorm : (2 : R) ^ FloatFormat.min_exp ≤ |x|
  · -- ═══════════════════════════════════════════════════════════════════
    -- Normal case: |x| ≥ 2^min_exp
    -- ═══════════════════════════════════════════════════════════════════
    have herr := nearest_abs_error_le_ulp_half_signed x hx_ne hnorm f hround
    -- Int.log 2 |x| ≤ M + g - 1 (since |x| < 2^(M+g))
    have hlog : Int.log 2 |x| ≤ (M : ℤ) + g - 1 := by
      rw [← Int.lt_add_one_iff, show (M : ℤ) + g - 1 + 1 = (M : ℤ) + g from by omega]
      exact (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hx_ne)).mp hx_abs_bound
    -- ulp(x) ≤ 2^(M + g - prec)
    have hulp : Fp.ulp x ≤ (2 : R) ^ ((M : ℤ) + g - prec) := by
      rw [Fp.ulp_normal_eq x hnorm]
      exact two_zpow_mono (R := R) (by omega)
    -- |x - f.toVal| ≤ ulp/2 ≤ 2^(M+g-prec-1) = 2^(M-prec-1) * 2^g
    have herr_bound : |x - f.toVal (R := R)| ≤
        (2 : R) ^ ((M : ℤ) - prec - 1) * (2 : R) ^ g := by
      have h1 : Fp.ulp x / 2 ≤ (2 : R) ^ ((M : ℤ) + g - prec) / 2 :=
        div_le_div_of_nonneg_right hulp (by norm_num)
      have h2 : (2 : R) ^ ((M : ℤ) + g - prec) / 2 =
          (2 : R) ^ ((M : ℤ) - prec - 1) * (2 : R) ^ g := by
        rw [show (M : ℤ) + g - prec = ((M : ℤ) - prec - 1 + g) + 1 from by omega,
            zpow_add_one₀ h2_ne, zpow_add₀ h2_ne]; ring
      linarith [herr]
    -- Divide by 2^g: |n - n'| ≤ 2^(M - prec - 1)
    have hcoeff : |((n - n' : ℤ) : R)| ≤ (2 : R) ^ ((M : ℤ) - prec - 1) := by
      rw [hdiff, abs_mul, abs_of_pos h2g_pos] at herr_bound
      nlinarith
    -- Convert R inequality to ℤ then ℕ
    -- Convert from R to ℤ then ℕ
    have hprec_eq : (precNat : ℤ) = prec := FloatFormat.prec_toNat_eq
    have hexp_eq : (M : ℤ) - prec - 1 = ↑(M - precNat - 1 : ℕ) := by
      rw [Nat.cast_sub (show 1 ≤ M - precNat from by omega),
          Nat.cast_sub (show precNat ≤ M from by omega), hprec_eq]; norm_cast
    have hcoeff_int : |(n - n' : ℤ)| ≤ (2 : ℤ) ^ (M - precNat - 1) := by
      have : (2 : R) ^ ((M : ℤ) - prec - 1) = ↑((2 : ℤ) ^ (M - precNat - 1 : ℕ)) := by
        rw [hexp_eq]; push_cast [zpow_natCast]; ring
      rw [← Int.cast_abs, this] at hcoeff; exact_mod_cast hcoeff
    exact_mod_cast show (↑(n - n').natAbs : ℤ) ≤ (2 : ℤ) ^ (M - precNat - 1) from by
      simp only [Int.natCast_natAbs]; linarith [abs_nonneg (n - n' : ℤ)]
  · -- ═══════════════════════════════════════════════════════════════════
    -- Subnormal case: |x| < 2^min_exp → round is exact → n' = n
    -- ═══════════════════════════════════════════════════════════════════
    push_neg at hnorm
    -- |n| < 2^prec (tighter than 2^M): from |x| < 2^min_exp and g ≥ min_exp - prec + 1
    have hn_small : n.natAbs < 2 ^ precNat := by
      by_contra h; push_neg at h
      -- If |n| ≥ 2^prec, then |x| = |n| * 2^g ≥ 2^prec * 2^(min_exp-prec+1) = 2^(min_exp+1) > 2^min_exp
      have : |x| ≥ (2 : R) ^ FloatFormat.min_exp := by
        rw [x_def, abs_mul, abs_of_pos h2g_pos]
        have h_int : (2 : ℤ) ^ precNat ≤ |n| := by
          calc (2 : ℤ) ^ precNat = ↑(2 ^ precNat : ℕ) := by push_cast; ring
            _ ≤ ↑n.natAbs := by exact_mod_cast h
            _ = |n| := Int.natCast_natAbs n
        have h_R : (2 : R) ^ (precNat : ℤ) ≤ |(n : R)| := by
          rw [← Int.cast_abs, zpow_natCast]; push_cast; exact_mod_cast h_int
        calc (2 : R) ^ FloatFormat.min_exp
            = (2 : R) ^ (precNat : ℤ) * (2 : R) ^ (FloatFormat.min_exp - prec) := by
              rw [← zpow_add₀ h2_ne]; congr 1
              have := FloatFormat.prec_toNat_eq; omega
          _ ≤ (2 : R) ^ (precNat : ℤ) * (2 : R) ^ g := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact two_zpow_mono (R := R) (by omega)
          _ ≤ |(n : R)| * (2 : R) ^ g :=
              mul_le_mul_of_nonneg_right h_R (le_of_lt h2g_pos)
      linarith
    -- Construct the representable witness
    obtain ⟨w, hw_valid, hw_val⟩ := exists_finiteFp_of_int_mul_zpow (R := R)
      n g hn_ne hn_small hg_ge (by omega)
    -- round(x) = round(w.toVal) = w (by idempotence)
    have hx_eq_w : x = w.toVal (R := R) := by rw [hw_val, x_def]
    have hw_round : ○x = Fp.finite w := by
      rw [hx_eq_w]; exact RModeIdem.round_idempotent (R := R) w hw_valid
    -- f = w, so f.toVal = x = n * 2^g, hence n' = n
    have hf_eq_w : f = w := Fp.finite.inj (hround.symm.trans hw_round)
    have hfv_eq : f.toVal (R := R) = x := by rw [hf_eq_w, ← hx_eq_w]
    have hn'_eq : n' = n := by
      have : ((n' : R) - n) * (2 : R) ^ g = 0 := by
        have := hfg.symm.trans hfv_eq; rw [x_def] at this; linarith
      have := (mul_eq_zero.mp this).resolve_right h2g_ne
      exact_mod_cast show (n' : R) = (n : R) from by linarith [this]
    simp [hn'_eq]

/-! ## Coefficient bound — the key technical lemma

The core argument: `a - a_hi = -(err_δ + err_hi)` where `err_δ` and `err_hi` are
rounding errors on grid `2^g`. Using `|round(x) - x| ≤ ulp(x)/2`:

- `|err_δ| ≤ 2^s` (from `ulp(a - γ) ≤ 2^(s+1) * 2^g` since `|a - γ| < 2^(s+1) * |a|`)
- `|err_hi| ≤ 1` (from `ulp(γ + δ) ≤ 2 * 2^g` since `|γ + δ| ≈ |a| < 2^(e+1)`)
- So `|m_a - n_hi| ≤ 2^s + 1 < 2^p` (for `s ≤ p - 1`)
-/

private theorem veltkamp_coeff_bound
    (s : ℤ) (hs_pos : 1 ≤ s) (hs_prec : s ≤ prec - 1)
    (m_a n_γ n_δ n_hi : ℤ)
    (hδ_err : ((m_a - n_γ) - n_δ).natAbs ≤ 2 ^ s.toNat)
    (hahi_err : ((n_γ + n_δ) - n_hi).natAbs ≤ 1) :
    (m_a - n_hi).natAbs < 2 ^ precNat := by
  -- Decompose: m_a - n_hi = ((m_a - n_γ) - n_δ) + ((n_γ + n_δ) - n_hi)
  have hdecomp : m_a - n_hi = ((m_a - n_γ) - n_δ) + ((n_γ + n_δ) - n_hi) := by ring
  have htri : (m_a - n_hi).natAbs ≤
      ((m_a - n_γ) - n_δ).natAbs + ((n_γ + n_δ) - n_hi).natAbs := by
    rw [hdecomp]; exact Int.natAbs_add_le _ _
  have hp : precNat ≥ 2 := by have := FloatFormat.valid_prec; omega
  have hs_nat : s.toNat ≤ precNat - 1 := by omega
  -- 2^s + 1 < 2^(s+1) ≤ 2^prec
  have hs_ne : s.toNat ≠ 0 := by omega
  have h_lt_succ : 2 ^ s.toNat + 1 < 2 ^ (s.toNat + 1) := by
    have : 1 < 2 ^ s.toNat := Nat.one_lt_pow hs_ne (by omega)
    rw [pow_succ]; linarith
  have h_succ_le : 2 ^ (s.toNat + 1) ≤ 2 ^ precNat :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc (m_a - n_hi).natAbs
      ≤ ((m_a - n_γ) - n_δ).natAbs + ((n_γ + n_δ) - n_hi).natAbs := htri
    _ ≤ 2 ^ s.toNat + 1 := Nat.add_le_add hδ_err hahi_err
    _ < 2 ^ precNat := lt_of_lt_of_le h_lt_succ h_succ_le

/-! ## Main exactness theorem -/

/-- **Veltkamp splitting exactness** (positive case).

For a positive normal float `a` and splitting constant `C` with value `2^s + 1`
where `1 ≤ s ≤ p - 1`, under round-to-nearest mode with no overflow in
intermediate computations, the Veltkamp splitting produces `a_hi + a_lo = a`.

The proof uses grid alignment: all intermediate values lie on a common grid `2^g`
(where `g = a.e - prec + 1`), and the difference `a - a_hi` has a small
enough integer coefficient to be exactly representable. -/
theorem veltkampSplit_exact (a C : FiniteFp)
    (ha : a.s = false) (ha_nz : 0 < a.m)
    (s : ℤ) (hs_pos : 1 ≤ s) (hs_prec : s ≤ prec - 1)
    (hC_val : C.toVal (R := R) = (2 : R) ^ s + 1)
    -- Grid validity: a's exponent is valid (implied by FiniteFp validity for normal a)
    (hg_valid : a.e - prec + 1 ≥ FloatFormat.min_exp - prec + 1)
    -- Rounding mode requirements
    [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeNearest R] [RModeConj R]
    -- Intermediate results (no overflow — each operation produces a finite float)
    (γ : FiniteFp) (hγ : C * a = γ)
    (δ : FiniteFp) (hδ : a - γ = δ)
    (a_hi : FiniteFp) (hahi : γ + δ = a_hi)
    (a_lo : FiniteFp) (halo : a - a_hi = a_lo) :
    (a_hi.toVal : R) + a_lo.toVal = a.toVal := by
  -- Set up the grid level
  set g := a.e - prec + 1 with g_def
  have hg_ge : g ≥ FloatFormat.min_exp - prec + 1 := hg_valid
  have ha_val_ne : (a.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos a ha_nz
  have h2g_ne : (2 : R) ^ g ≠ 0 := zpow_ne_zero _ (by norm_num)
  -- Step 1: a is on grid 2^g with coefficient m_a, where |m_a| < 2^p
  obtain ⟨m_a, hm_a⟩ := FiniteFp.toVal_int_mul_zpow (R := R) a ha g (by omega)
  -- Step 2: The exact product C*a = (2^s + 1)*a is on grid 2^g
  set n_prod := (2 ^ s.toNat + 1 : ℤ) * m_a with n_prod_def
  have hn_prod : (C.toVal : R) * a.toVal = (n_prod : R) * (2 : R) ^ g := by
    rw [hC_val, hm_a, n_prod_def]
    push_cast
    rw [← zpow_natCast (2 : R) s.toNat, show (s.toNat : ℤ) = s from by omega]
    ring
  -- Step 3: γ = round(C * a) is on grid 2^g by RModeGrid
  have hγ_corr : (γ : Fp) = ○(C.toVal (R := R) * a.toVal) := by
    have hprod_ne : (C.toVal : R) * a.toVal ≠ 0 :=
      mul_ne_zero (by rw [hC_val]; positivity) ha_val_ne
    have := fpMulFinite_correct (R := R) C a hprod_ne
    simp only [mul_finite_eq_fpMulFinite, mul_eq_fpMul, fpMul] at this hγ
    rw [this] at hγ; exact hγ.symm
  have hγ_round : ○((n_prod : R) * (2 : R) ^ g) = Fp.finite γ := by
    rw [← hn_prod]; exact hγ_corr.symm
  obtain ⟨n_γ, hn_γ⟩ := RModeGrid.round_preserves_grid n_prod g hg_ge γ hγ_round
  -- Step 4: δ = round(a - γ) is on grid 2^g
  have ha_sub_γ : (a.toVal : R) - γ.toVal = ((m_a - n_γ : ℤ) : R) * (2 : R) ^ g := by
    push_cast; rw [hm_a, hn_γ]; ring
  -- Case split: is a - γ zero?
  by_cases hdiff_ne : (a.toVal : R) - γ.toVal = 0
  · -- ══════════════════════════════════════════════════════════════════════
    -- Trivial case: a.toVal = γ.toVal
    -- ══════════════════════════════════════════════════════════════════════
    have ha_eq_γ : (a.toVal : R) = γ.toVal := sub_eq_zero.mp hdiff_ne
    -- δ.toVal = 0 via fpSubFinite_zero_of_eq_toVal
    obtain ⟨fδ, hfδ_eq, hfδ_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a γ ha_eq_γ
    have hδ_zero : (δ.toVal : R) = 0 :=
      (toVal_of_fp_eq (R := R) δ fδ (hδ.symm.trans hfδ_eq)).trans hfδ_val
    -- γ + δ has γ.toVal + δ.toVal = γ.toVal, so a_hi has the same value
    have hγδ_eq_γ : (γ.toVal : R) + δ.toVal = γ.toVal := by rw [hδ_zero, add_zero]
    -- γ must have nonzero m (since γ.toVal = a.toVal ≠ 0)
    have hγ_nz : 0 < γ.m := by
      by_contra h; push_neg at h
      have hγ_m_zero : γ.m = 0 := by omega
      have : (γ.toVal : R) = 0 := FiniteFp.toVal_isZero (show γ.isZero from hγ_m_zero)
      rw [this] at ha_eq_γ; exact ha_val_ne ha_eq_γ
    -- a_hi.toVal = γ.toVal (round of a representable value)
    have hγ_val_ne : (γ.toVal : R) ≠ 0 := FiniteFp.toVal_ne_zero_of_m_pos γ hγ_nz
    have hahi_corr : (a_hi : Fp) = ○((γ.toVal : R) + δ.toVal) := by
      have hne : (γ.toVal : R) + δ.toVal ≠ 0 := by rw [hγδ_eq_γ]; exact hγ_val_ne
      have := fpAddFinite_correct (R := R) γ δ hne
      simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at this hahi
      rw [this] at hahi; exact hahi.symm
    have hahi_val : (a_hi.toVal : R) = γ.toVal := by
      rw [hγδ_eq_γ] at hahi_corr
      have hγ_idem := RModeIdem.round_idempotent (R := R) γ (Or.inr hγ_nz)
      rw [hγ_idem] at hahi_corr
      exact toVal_of_fp_eq (R := R) a_hi γ hahi_corr
    -- a_lo = round(a - a_hi) = round(0) → a_lo.toVal = 0
    have ha_eq_ahi : (a.toVal : R) = a_hi.toVal := by rw [hahi_val]; exact ha_eq_γ
    obtain ⟨flo, hflo_eq, hflo_val⟩ := fpSubFinite_zero_of_eq_toVal (R := R) a a_hi ha_eq_ahi
    have halo_zero : (a_lo.toVal : R) = 0 :=
      (toVal_of_fp_eq (R := R) a_lo flo (halo.symm.trans hflo_eq)).trans hflo_val
    linarith
  · -- ══════════════════════════════════════════════════════════════════════
    -- Main case: a - γ ≠ 0
    -- ══════════════════════════════════════════════════════════════════════
    have hδ_corr : (δ : Fp) = ○((a.toVal : R) - γ.toVal) := by
      have := fpSubFinite_correct (R := R) a γ hdiff_ne
      simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at this hδ
      rw [this] at hδ; exact hδ.symm
    have hδ_round : ○(((m_a - n_γ : ℤ) : R) * (2 : R) ^ g) = Fp.finite δ := by
      rw [← ha_sub_γ]; exact hδ_corr.symm
    obtain ⟨n_δ, hn_δ⟩ := RModeGrid.round_preserves_grid (m_a - n_γ) g hg_ge δ hδ_round
    -- Step 5: a_hi = round(γ + δ)
    have hγ_add_δ : (γ.toVal : R) + δ.toVal = ((n_γ + n_δ : ℤ) : R) * (2 : R) ^ g := by
      push_cast; rw [hn_γ, hn_δ]; ring
    -- Case split on γ + δ = 0
    by_cases hsum_ne : (γ.toVal : R) + δ.toVal = 0
    · -- ════════════════════════════════════════════════════════════════════
      -- Subcase: γ + δ = 0
      -- ════════════════════════════════════════════════════════════════════
      -- a_hi = round(γ + δ) where γ.toVal + δ.toVal = 0
      obtain ⟨fhi, hfhi_eq, hfhi_val⟩ := fpAddFinite_zero_of_eq_sum (R := R) γ δ hsum_ne
      have hahi_zero : (a_hi.toVal : R) = 0 :=
        (toVal_of_fp_eq (R := R) a_hi fhi (hahi.symm.trans hfhi_eq)).trans hfhi_val
      -- a_lo = round(a - 0) = round(a) = a (by idempotence)
      have hdiff_ne' : (a.toVal : R) - a_hi.toVal ≠ 0 := by
        rw [hahi_zero, sub_zero]; exact ha_val_ne
      have halo_corr : (a_lo : Fp) = ○((a.toVal : R) - a_hi.toVal) := by
        have := fpSubFinite_correct (R := R) a a_hi hdiff_ne'
        simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at this halo
        rw [this] at halo; exact halo.symm
      rw [hahi_zero, sub_zero] at halo_corr
      have ha_idem := RModeIdem.round_idempotent (R := R) a (Or.inl ha)
      rw [ha_idem] at halo_corr
      have halo_val : (a_lo.toVal : R) = a.toVal :=
        toVal_of_fp_eq (R := R) a_lo a halo_corr
      linarith [hahi_zero]
    · -- ════════════════════════════════════════════════════════════════════
      -- Main subcase: a - γ ≠ 0 and γ + δ ≠ 0
      -- ════════════════════════════════════════════════════════════════════
      have hahi_corr : (a_hi : Fp) = ○((γ.toVal : R) + δ.toVal) := by
        have := fpAddFinite_correct (R := R) γ δ hsum_ne
        simp only [add_finite_eq_fpAddFinite, add_eq_fpAdd, fpAdd_coe_coe] at this hahi
        rw [this] at hahi; exact hahi.symm
      have hahi_round : ○(((n_γ + n_δ : ℤ) : R) * (2 : R) ^ g) = Fp.finite a_hi := by
        rw [← hγ_add_δ]; exact hahi_corr.symm
      obtain ⟨n_hi, hn_hi⟩ :=
        RModeGrid.round_preserves_grid (n_γ + n_δ) g hg_ge a_hi hahi_round
      -- Step 6: a - a_hi = (m_a - n_hi) * 2^g on grid 2^g
      have ha_sub_ahi : (a.toVal : R) - a_hi.toVal =
          ((m_a - n_hi : ℤ) : R) * (2 : R) ^ g := by
        push_cast; rw [hm_a, hn_hi]; ring
      -- Step 7: Bound |m_a - n_hi| < 2^prec via ULP/2 nearest-rounding error
      -- First establish m_a facts
      have hm_a_ne : m_a ≠ 0 := by
        intro h; rw [h, Int.cast_zero, zero_mul] at hm_a; exact ha_val_ne hm_a
      have hm_a_pos : 0 < m_a := by
        rcases lt_or_gt_of_ne hm_a_ne with h | h
        · have : (a.toVal : R) < 0 := by
            rw [hm_a]; exact mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr h) (by positivity)
          linarith [FiniteFp.toVal_nonneg (R := R) a ha]
        · exact h
      have hm_a_bound : m_a.natAbs < 2 ^ precNat := by
        -- m_a = a.m since g = a.e - prec + 1
        have hav := FiniteFp.toVal_factor_zpow (R := R) a ha g
        simp only [g_def, sub_self, zpow_zero, mul_one] at hav
        have hm_eq : (m_a : R) = (a.m : R) :=
          mul_right_cancel₀ h2g_ne (hm_a.symm.trans hav)
        have hm_eq_int : m_a = (a.m : ℤ) := by exact_mod_cast hm_eq
        simp only [hm_eq_int, Int.natAbs_natCast]; exact a.valid.2.2.1
      -- Bound |m_a - n_γ| < 2^(s + prec + 1) via γ's rounding error
      have hn_prod_ne : n_prod ≠ 0 := by
        rw [n_prod_def]; exact mul_ne_zero (by positivity) (ne_of_gt hm_a_pos)
      have hm_a_lt_int : m_a < (2 : ℤ) ^ precNat := by
        have : (m_a.natAbs : ℤ) < (2 ^ precNat : ℤ) := by exact_mod_cast hm_a_bound
        rwa [Int.natAbs_of_nonneg (le_of_lt hm_a_pos)] at this
      have hn_prod_bound : n_prod.natAbs < 2 ^ (s.toNat + precNat + 1) := by
        have h_pos : 0 ≤ n_prod := by rw [n_prod_def]; positivity
        have h_natabs : (n_prod.natAbs : ℤ) = n_prod := Int.natAbs_of_nonneg h_pos
        have h2s : (2 : ℤ) ^ s.toNat + 1 ≤ 2 ^ (s.toNat + 1) := by
          have : (1 : ℤ) ≤ 2 ^ s.toNat := one_le_pow₀ (by omega : (1 : ℤ) ≤ 2)
          rw [pow_succ]; omega
        have : n_prod < (2 : ℤ) ^ (s.toNat + precNat + 1) :=
          calc n_prod = (2 ^ s.toNat + 1) * m_a := n_prod_def
            _ < (2 ^ s.toNat + 1) * 2 ^ precNat := by
                apply mul_lt_mul_of_pos_left hm_a_lt_int; positivity
            _ ≤ 2 ^ (s.toNat + 1) * 2 ^ precNat :=
                mul_le_mul_of_nonneg_right h2s (by positivity)
            _ = 2 ^ (s.toNat + precNat + 1) := by rw [← pow_add]; ring_nf
        exact_mod_cast show (n_prod.natAbs : ℤ) < (2 : ℤ) ^ (s.toNat + precNat + 1) by omega
      have hγ_err : (n_prod - n_γ).natAbs ≤ 2 ^ s.toNat := by
        have h := nearest_grid_coeff_error n_prod g γ n_γ (s.toNat + precNat + 1)
          hg_ge (by have := a.valid.2.1; omega) hn_prod_ne hn_prod_bound (by omega) hγ_round hn_γ
        simp only [show s.toNat + precNat + 1 - precNat - 1 = s.toNat from by omega] at h
        exact h
      -- From γ error, bound |m_a - n_γ|
      have hma_nγ_bound : (m_a - n_γ).natAbs < 2 ^ (s.toNat + precNat + 1) := by
        -- m_a - n_γ = (m_a - n_prod) + (n_prod - n_γ)
        have hdecomp : m_a - n_γ = (m_a - n_prod) + (n_prod - n_γ) := by ring
        -- m_a - n_prod = -(2^s * m_a), so |m_a - n_prod| = 2^s * m_a
        have hmp : m_a - n_prod = -(2 ^ s.toNat : ℤ) * m_a := by rw [n_prod_def]; ring
        have hmp_natabs : (m_a - n_prod).natAbs = 2 ^ s.toNat * m_a.natAbs := by
          simp [hmp, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow]
        calc (m_a - n_γ).natAbs
            ≤ (m_a - n_prod).natAbs + (n_prod - n_γ).natAbs := by
              rw [hdecomp]; exact Int.natAbs_add_le _ _
          _ = 2 ^ s.toNat * m_a.natAbs + (n_prod - n_γ).natAbs := by rw [hmp_natabs]
          _ ≤ 2 ^ s.toNat * m_a.natAbs + 2 ^ s.toNat := Nat.add_le_add_left hγ_err _
          _ = 2 ^ s.toNat * (m_a.natAbs + 1) := by ring
          _ ≤ 2 ^ s.toNat * 2 ^ precNat :=
              Nat.mul_le_mul_left _ hm_a_bound
          _ = 2 ^ (s.toNat + precNat) := by rw [← pow_add]
          _ < 2 ^ (s.toNat + precNat + 1) :=
              Nat.pow_lt_pow_right (by omega) (by omega)
      -- Apply nearest_grid_coeff_error to δ's rounding
      have hma_nγ_ne : m_a - n_γ ≠ 0 := by
        intro h; have : (m_a - n_γ : ℤ) = 0 := h
        have : ((m_a - n_γ : ℤ) : R) * (2 : R) ^ g = 0 :=
          by rw [this, Int.cast_zero, zero_mul]
        rw [← ha_sub_γ] at this; exact hdiff_ne this
      have hδ_err : ((m_a - n_γ) - n_δ).natAbs ≤ 2 ^ s.toNat := by
        have h := nearest_grid_coeff_error (m_a - n_γ) g δ n_δ (s.toNat + precNat + 1)
          hg_ge (by have := a.valid.2.1; omega) hma_nγ_ne hma_nγ_bound (by omega) hδ_round hn_δ
        simp only [show s.toNat + precNat + 1 - precNat - 1 = s.toNat from by omega] at h
        exact h
      -- Bound |n_γ + n_δ| < 2^(prec + 1) from δ error
      have hnγnδ_bound : (n_γ + n_δ).natAbs < 2 ^ (precNat + 1) := by
        -- n_γ + n_δ = m_a - ((m_a - n_γ) - n_δ)
        have hdecomp : n_γ + n_δ = m_a + (-((m_a - n_γ) - n_δ)) := by ring
        rw [hdecomp]
        have hδ_lt : ((m_a - n_γ) - n_δ).natAbs < 2 ^ precNat :=
          calc ((m_a - n_γ) - n_δ).natAbs
              ≤ 2 ^ s.toNat := hδ_err
            _ ≤ 2 ^ (precNat - 1) := Nat.pow_le_pow_right (by omega) (by omega)
            _ < 2 ^ precNat := Nat.pow_lt_pow_right (by omega) (by omega)
        calc (m_a + -((m_a - n_γ) - n_δ)).natAbs
            ≤ m_a.natAbs + (-((m_a - n_γ) - n_δ)).natAbs := Int.natAbs_add_le _ _
          _ = m_a.natAbs + ((m_a - n_γ) - n_δ).natAbs := by rw [Int.natAbs_neg]
          _ < 2 ^ precNat + 2 ^ precNat := Nat.add_lt_add hm_a_bound hδ_lt
          _ = 2 ^ (precNat + 1) := by rw [pow_succ]; ring
      -- Apply nearest_grid_coeff_error to a_hi's rounding
      have hnγnδ_ne : n_γ + n_δ ≠ 0 := by
        intro h; have : ((n_γ + n_δ : ℤ) : R) * (2 : R) ^ g = 0 := by
          rw [show (n_γ + n_δ : ℤ) = 0 from h, Int.cast_zero, zero_mul]
        rw [← hγ_add_δ] at this; exact hsum_ne this
      have hahi_err : ((n_γ + n_δ) - n_hi).natAbs ≤ 1 := by
        have h := nearest_grid_coeff_error (n_γ + n_δ) g a_hi n_hi (precNat + 1)
          hg_ge (by have := a.valid.2.1; omega) hnγnδ_ne hnγnδ_bound (by omega) hahi_round hn_hi
        simp only [show precNat + 1 - precNat - 1 = 0 from by omega, pow_zero] at h
        exact h
      have hcoeff_bound : (m_a - n_hi).natAbs < 2 ^ precNat :=
        veltkamp_coeff_bound s hs_pos hs_prec m_a n_γ n_δ n_hi hδ_err hahi_err
      -- Step 8: a - a_hi is representable → final subtraction is exact
      by_cases hcoeff_zero : m_a - n_hi = 0
      · -- a = a_hi in value, so a_lo = round(0) = 0
        have ha_eq_ahi : (a.toVal : R) = a_hi.toVal := by
          have : (a.toVal : R) - a_hi.toVal = 0 := by
            rw [ha_sub_ahi, hcoeff_zero]; simp
          linarith
        obtain ⟨flo, hflo_eq, hflo_val⟩ :=
          fpSubFinite_zero_of_eq_toVal (R := R) a a_hi ha_eq_ahi
        have halo_zero : (a_lo.toVal : R) = 0 :=
          (toVal_of_fp_eq (R := R) a_lo flo (halo.symm.trans hflo_eq)).trans hflo_val
        linarith
      · -- a ≠ a_hi, construct the representable witness
        obtain ⟨f, hf_valid, hfv⟩ := exists_finiteFp_of_int_mul_zpow (R := R)
          (m_a - n_hi) g hcoeff_zero hcoeff_bound
          (by omega) (by have := a.valid.2.1; omega)
        -- a_lo = round(a - a_hi) = round(f.toVal) = f (by idempotence)
        have hdiff_ne' : (a.toVal : R) - a_hi.toVal ≠ 0 := by
          rw [ha_sub_ahi]; exact mul_ne_zero (Int.cast_ne_zero.mpr hcoeff_zero) h2g_ne
        have halo_eq : (a_lo : Fp) = Fp.finite f := by
          have := fpSubFinite_correct (R := R) a a_hi hdiff_ne'
          simp only [sub_finite_eq_fpSubFinite, sub_eq_fpSub, fpSub_coe_coe] at this halo
          rw [this] at halo
          rw [← halo, ha_sub_ahi, ← hfv,
              RModeIdem.round_idempotent (R := R) f hf_valid]
        have halo_val : (a_lo.toVal : R) = a.toVal - a_hi.toVal := by
          have halo_is_f : a_lo = f := Fp.finite.inj halo_eq
          rw [halo_is_f, hfv]; linarith [ha_sub_ahi]
        linarith

end VeltkampSplit
