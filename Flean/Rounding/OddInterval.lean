import Flean.Rounding.Rounding
import Flean.Rounding.RoundDown
import Flean.Rounding.RoundUp
import Flean.Rounding.RoundNearest

/-! # Odd Interval Lemmas for Rounding

Helper lemmas for proving roundNearest modes are constant on odd intervals.
-/

section OddInterval

variable [FloatFormat]

/-- A positive representable float with value `k * 2^e_base` where `k > 2^prec`
    must have `k` divisible by a power of 2, specifically `2^d` divides `k`
    where `d = f.e - prec + 1 - e_base ≥ 1`. Here we prove `d ≥ 1` implies `2 ∣ k`. -/
private theorem representable_value_even_of_large {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {k : ℕ} {e_base : ℤ}
    (hk_large : 2 ^ FloatFormat.prec.toNat < k)
    (f : FiniteFp) (hfs : f.s = false) (hfm : 0 < f.m)
    (hfval : (f.toVal : R) = (k : R) * (2 : R) ^ e_base) :
    ∃ d : ℕ, 0 < d ∧ f.m * 2 ^ d = k := by
  have htoVal : (f.toVal : R) = ↑f.m * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hfs]; simp
  rw [htoVal] at hfval
  set d := f.e - FloatFormat.prec + 1 - e_base with hd_def
  have hexp_eq : f.e - FloatFormat.prec + 1 = e_base + d := by omega
  rw [hexp_eq, zpow_add₀ (by norm_num : (2:R) ≠ 0)] at hfval
  have hE_ne : (2 : R) ^ e_base ≠ 0 := ne_of_gt (zpow_pos (by norm_num : (0:R) < 2) _)
  have hfm_2d_eq : (↑f.m : R) * (2 : R) ^ d = (k : R) := by
    have h := hfval -- f.m * (2^e_base * 2^d) = k * 2^e_base
    have : (↑f.m : R) * (2:R)^d * (2:R)^e_base = (k : R) * (2:R)^e_base := by linarith
    exact mul_right_cancel₀ hE_ne this
  have hm_bound : f.m < 2 ^ FloatFormat.prec.toNat := f.valid.2.2.1
  -- d > 0 because f.m < 2^prec < k
  have hd_pos : 0 < d := by
    by_contra hd_le; push_neg at hd_le
    have h1 : (↑f.m : R) * (2 : R) ^ d ≤ ↑f.m := by
      calc (↑f.m : R) * (2:R)^d ≤ ↑f.m * 1 := by
            gcongr; exact zpow_le_one_of_nonpos₀ (by norm_num : (1:R) ≤ 2) hd_le
        _ = ↑f.m := mul_one _
    linarith [show (↑f.m : R) < (k : R) from by exact_mod_cast (show f.m < k from by omega)]
  -- Convert to natural number equation
  have hd_nat_pos : 0 < d.toNat := by omega
  have hfm_2d_nat_eq : f.m * 2 ^ d.toNat = k := by
    have : (↑(f.m * 2 ^ d.toNat) : R) = (k : R) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast (2 : R) d.toNat,
          Int.toNat_of_nonneg (by omega : 0 ≤ d)]
      exact hfm_2d_eq
    exact_mod_cast this
  exact ⟨d.toNat, hd_nat_pos, hfm_2d_nat_eq⟩

/-- A representable value `k * 2^e_base` with `k > (2^prec - 1) * 8` has `16 ∣ k`. -/
theorem representable_value_div_16 {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {k : ℕ} {e_base : ℤ}
    (hk_large : (2 ^ FloatFormat.prec.toNat - 1) * 8 < k)
    (f : FiniteFp) (hfs : f.s = false) (hfm : 0 < f.m)
    (hfval : (f.toVal : R) = (k : R) * (2 : R) ^ e_base) :
    16 ∣ k := by
  set p := FloatFormat.prec.toNat with hp_def
  have hp_pos : 0 < 2 ^ p := Nat.pos_of_ne_zero (by positivity)
  have h8p : 2 ^ p ≤ (2 ^ p - 1) * 8 := by
    have h4 : 4 ≤ 2 ^ p := by
      have := FloatFormat.valid_prec; rw [hp_def]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hk_prec : 2 ^ p < k := lt_of_le_of_lt h8p hk_large
  obtain ⟨d, hd_pos, hd_eq⟩ := representable_value_even_of_large hk_prec f hfs hfm hfval
  have hm_bound : f.m < 2 ^ p := f.valid.2.2.1
  have hd_ge : 4 ≤ d := by
    by_contra h; push_neg at h
    have hd_le3 : 2 ^ d ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : k ≤ (2 ^ p - 1) * 2 ^ 3 := by
      calc k = f.m * 2 ^ d := hd_eq.symm
        _ ≤ f.m * 2 ^ 3 := Nat.mul_le_mul_left _ hd_le3
        _ ≤ (2 ^ p - 1) * 2 ^ 3 := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [← hd_eq]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd_ge) _

omit [FloatFormat] in
/-- The sum of two multiples of 16 cannot equal `2*n` when `n` is odd.
    Key: `16 ∣ (a+b)` implies `4 ∣ (a+b)`, but `n` odd means `2n ≡ 2 (mod 4)`. -/
theorem sum_ne_double_odd {a b n : ℕ} (hn_odd : n % 2 = 1)
    (h16a : 16 ∣ a) (h16b : 16 ∣ b) : a + b ≠ 2 * n := by omega

omit [FloatFormat] in
/-- Two even numbers `a` and `b` with `a + 2 = b` cannot both be divisible by 4.
    (Because `b - a = 2` and `4 ∤ 2`.) -/
private theorem not_both_div_four {a b : ℕ} (hab : a + 2 = b)
    (ha4 : 4 ∣ a) (hb4 : 4 ∣ b) : False := by omega

/-- The boundaries `(n-1)*E` and `(n+1)*E` of an odd interval cannot both be representable
    when `n > 2^(prec+3)`, because both boundaries being representable would require
    `2^4 ∣ (n-1)` and `2^4 ∣ (n+1)`, but `(n+1) - (n-1) = 2` is not divisible by 16. -/
theorem not_both_boundary_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n) :
    ¬(∃ f : FiniteFp, f.s = false ∧ 0 < f.m ∧
        (f.toVal : R) = ((n : ℤ) - 1 : R) * (2 : R) ^ e_base) ∨
    ¬(∃ g : FiniteFp, g.s = false ∧ 0 < g.m ∧
        (g.toVal : R) = ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨f, hfs, hfm, hfval⟩, ⟨g, hgs, hgm, hgval⟩⟩ := h
  -- n - 1 and n + 1 as natural numbers (n ≥ 2)
  have hn_ge : 2 ≤ n := by
    have : 0 < 2 ^ (FloatFormat.prec.toNat + 3) := Nat.pos_of_ne_zero (by positivity)
    omega
  -- Cast cleanup
  have hn1_cast : ((n : ℤ) - 1 : R) = ((n - 1 : ℕ) : R) := by
    have h : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have : ((n - 1 : ℕ) : R) = ((n : ℤ) - 1 : R) := by exact_mod_cast h
    exact this.symm
  have hf_cast : (f.toVal : R) = ((n - 1 : ℕ) : R) * (2 : R) ^ e_base := by
    rw [hfval, hn1_cast]
  have hg_cast : (g.toVal : R) = ((n + 1 : ℕ) : R) * (2 : R) ^ e_base := by
    rw [hgval]; congr 1; push_cast; ring
  set p := FloatFormat.prec.toNat with hp_def
  have hn1_large : 2 ^ p < n - 1 := by
    have hpow : 2 ^ (p + 3) = 2 ^ p * 2 ^ 3 := Nat.pow_add 2 p 3
    have hp_pos : 0 < 2 ^ p := Nat.pos_of_ne_zero (by positivity)
    omega
  have hn2_large : 2 ^ p < n + 1 := by omega
  -- Both n-1 and n+1 factor as f.m * 2^d with d ≥ 1
  obtain ⟨d₁, hd₁_pos, hd₁_eq⟩ := representable_value_even_of_large hn1_large f hfs hfm hf_cast
  obtain ⟨d₂, hd₂_pos, hd₂_eq⟩ := representable_value_even_of_large hn2_large g hgs hgm hg_cast
  have hm_f_bound : f.m < 2 ^ p := f.valid.2.2.1
  have hm_g_bound : g.m < 2 ^ p := g.valid.2.2.1
  -- d₁ ≥ 4: f.m * 2^d₁ = n-1 > 2^(p+3), f.m < 2^p, so 2^d₁ > 8
  have hd₁_ge : 4 ≤ d₁ := by
    by_contra h; push_neg at h
    have hd₁_le3 : 2 ^ d₁ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : n - 1 ≤ (2 ^ p - 1) * 2 ^ 3 := by
      calc n - 1 = f.m * 2 ^ d₁ := hd₁_eq.symm
        _ ≤ f.m * 2 ^ 3 := Nat.mul_le_mul_left _ hd₁_le3
        _ ≤ (2 ^ p - 1) * 2 ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have hpow : 2 ^ (p + 3) = 2 ^ p * 2 ^ 3 := by rw [Nat.pow_add]
    omega
  have hd₂_ge : 4 ≤ d₂ := by
    by_contra h; push_neg at h
    have hd₂_le3 : 2 ^ d₂ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : n + 1 ≤ (2 ^ p - 1) * 2 ^ 3 := by
      calc n + 1 = g.m * 2 ^ d₂ := hd₂_eq.symm
        _ ≤ g.m * 2 ^ 3 := Nat.mul_le_mul_left _ hd₂_le3
        _ ≤ (2 ^ p - 1) * 2 ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have hpow : 2 ^ (p + 3) = 2 ^ p * 2 ^ 3 := by rw [Nat.pow_add]
    omega
  -- 2^4 ∣ (n-1) and 2^4 ∣ (n+1)
  have h16_n1 : 2 ^ 4 ∣ (n - 1) := by
    rw [← hd₁_eq]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd₁_ge) _
  have h16_n2 : 2 ^ 4 ∣ (n + 1) := by
    rw [← hd₂_eq]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd₂_ge) _
  -- But (n+1) - (n-1) = 2, and 16 ∤ 2
  have h_sub : n + 1 - (n - 1) = 2 := by omega
  have : 16 ∣ (n + 1 - (n - 1)) := Nat.dvd_sub h16_n2 h16_n1
  rw [h_sub] at this
  omega

/-- Two values `a*E` and `b*E` with `a, b > 2^prec` and `b - a < 16` cannot both be
    representable. Generalization of `not_both_boundary_representable`. -/
theorem not_both_representable_close {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {a b : ℕ} {e_base : ℤ}
    (ha_large : (2 ^ FloatFormat.prec.toNat - 1) * 8 < a)
    (hb_large : (2 ^ FloatFormat.prec.toNat - 1) * 8 < b)
    (hab : a < b) (hgap : b - a < 16) :
    ¬(∃ f : FiniteFp, f.s = false ∧ 0 < f.m ∧
        (f.toVal : R) = (a : R) * (2 : R) ^ e_base) ∨
    ¬(∃ g : FiniteFp, g.s = false ∧ 0 < g.m ∧
        (g.toVal : R) = (b : R) * (2 : R) ^ e_base) := by
  by_contra h; push_neg at h
  obtain ⟨⟨f, hfs, hfm, hfval⟩, ⟨g, hgs, hgm, hgval⟩⟩ := h
  set p := FloatFormat.prec.toNat with hp_def
  have hp_pos : 0 < 2 ^ p := Nat.pos_of_ne_zero (by positivity)
  have hprec_ge : 2 ≤ p := by
    have := FloatFormat.valid_prec; rw [hp_def]; omega
  have h8p : 2 ^ p ≤ (2 ^ p - 1) * 8 := by
    have h4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hprec_ge
    omega
  have ha_prec : 2 ^ p < a := lt_of_le_of_lt h8p ha_large
  have hb_prec : 2 ^ p < b := lt_of_le_of_lt h8p hb_large
  obtain ⟨d₁, hd₁_pos, hd₁_eq⟩ := representable_value_even_of_large ha_prec f hfs hfm hfval
  obtain ⟨d₂, hd₂_pos, hd₂_eq⟩ := representable_value_even_of_large hb_prec g hgs hgm hgval
  have hm_f : f.m < 2 ^ p := f.valid.2.2.1
  have hm_g : g.m < 2 ^ p := g.valid.2.2.1
  have hpow_split : 2 ^ (p + 3) = 2 ^ p * 2 ^ 3 := Nat.pow_add 2 p 3
  have hd₁_ge : 4 ≤ d₁ := by
    by_contra h; push_neg at h
    have : a ≤ (2 ^ p - 1) * 2 ^ 3 := by
      calc a = f.m * 2 ^ d₁ := hd₁_eq.symm
        _ ≤ f.m * 2 ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ (2 ^ p - 1) * 2 ^ 3 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hd₂_ge : 4 ≤ d₂ := by
    by_contra h; push_neg at h
    have : b ≤ (2 ^ p - 1) * 2 ^ 3 := by
      calc b = g.m * 2 ^ d₂ := hd₂_eq.symm
        _ ≤ g.m * 2 ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ (2 ^ p - 1) * 2 ^ 3 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h16_a : 16 ∣ a := by rw [← hd₁_eq]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd₁_ge) _
  have h16_b : 16 ∣ b := by rw [← hd₂_eq]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd₂_ge) _
  have : 16 ∣ (b - a) := Nat.dvd_sub h16_b h16_a
  omega

omit [FloatFormat] in
/-- Midpoint of (rd, ru) is ≤ (n-1)*E when rd ≤ (n-3)*E and ru ≤ (n+1)*E. -/
theorem mid_le_of_rd_low_ru_tight {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ} {rd_val ru_val : R}
    (hrd_le : rd_val ≤ ((n : ℤ) - 3 : R) * (2 : R) ^ e_base)
    (hru_le : ru_val ≤ ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) :
    (rd_val + ru_val) / 2 ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base := by
  have hE : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  have h : rd_val + ru_val ≤ ((n : ℤ) - 3 : R) * (2:R)^e_base + ((n : ℤ) + 1 : R) * (2:R)^e_base :=
    add_le_add hrd_le hru_le
  have h2 : ((n : ℤ) - 3 : R) * (2:R)^e_base + ((n : ℤ) + 1 : R) * (2:R)^e_base =
      2 * (((n : ℤ) - 1 : R) * (2:R)^e_base) := by ring
  linarith

omit [FloatFormat] in
/-- Midpoint of (rd, ru) is ≥ (n+1)*E when rd ≥ (n-1)*E and ru ≥ (n+3)*E. -/
theorem mid_ge_of_rd_tight_ru_high {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ} {rd_val ru_val : R}
    (hrd_ge : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base ≤ rd_val)
    (hru_ge : ((n : ℤ) + 3 : R) * (2 : R) ^ e_base ≤ ru_val) :
    ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (rd_val + ru_val) / 2 := by
  have h : ((n : ℤ) - 1 : R) * (2:R)^e_base + ((n : ℤ) + 3 : R) * (2:R)^e_base ≤
      rd_val + ru_val := add_le_add hrd_ge hru_ge
  have h2 : ((n : ℤ) - 1 : R) * (2:R)^e_base + ((n : ℤ) + 3 : R) * (2:R)^e_base =
      2 * (((n : ℤ) + 1 : R) * (2:R)^e_base) := by ring
  linarith

/-- The overflow threshold `(2 - 2^(1-prec)/2) * 2^max_exp` cannot lie strictly inside
    an odd interval `((n-1)*E, (n+1)*E)` when `n` is odd and `n > 2^(prec+3)`.

    Key argument: OT/E = 2^a - 2^b where a = max_exp+1-e_base, b = a-(prec+1).
    - b ≥ 1: OT/E is an even integer, can't equal odd n.
    - b = 0: OT/E = 2^(prec+1)-1 < 2^(prec+3) < n.
    - b < 0: a < prec+1, so OT/E < 2^(prec+1), hence < n. -/
theorem overflow_threshold_outside_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hlo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base <
      FloatFormat.overflowThreshold R)
    (hhi : FloatFormat.overflowThreshold R <
      ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) : False := by
  -- OT = 2^(max_exp+1) - 2^(max_exp-prec). Rewrite in terms of E = 2^e_base.
  set OT := FloatFormat.overflowThreshold R with hOT_def
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  -- OT = (2^(max_exp+1) - 2^(max_exp-prec)). Factor as (2^a - 2^b) * E where a,b ≥ 0.
  -- Actually work with: (n-1)*E < OT < (n+1)*E, divide by E: n-1 < OT/E < n+1.
  -- OT/E = 2^(max_exp+1-e_base) - 2^(max_exp-prec-e_base).
  set a := FloatFormat.max_exp + 1 - e_base with ha_def
  set b := FloatFormat.max_exp - FloatFormat.prec - e_base with hb_def
  -- Show OT = (2^a - 2^b) * 2^e_base
  -- OT = (2 - 2^(1-prec)/2) * 2^max_exp = 2^(max_exp+1) - 2^(max_exp-prec)
  --    = 2^a * 2^e_base - 2^b * 2^e_base = (2^a - 2^b) * 2^e_base
  have hOT_factored : OT = ((2 : R) ^ a - (2 : R) ^ b) * (2 : R) ^ e_base := by
    rw [hOT_def]
    have h2ne : (2 : R) ≠ 0 := by norm_num
    -- 2^(1-prec)/2 * 2^max_exp = 2^(max_exp-prec)
    have hterm : (2:R)^(1-(FloatFormat.prec:ℤ))/2 * (2:R)^FloatFormat.max_exp =
        (2:R)^(FloatFormat.max_exp - FloatFormat.prec) := by
      have h1 : (2:R)^(1-(FloatFormat.prec:ℤ)) = (2:R)^(-(FloatFormat.prec:ℤ)) * 2 := by
        rw [show (1:ℤ)-(FloatFormat.prec:ℤ) = -(FloatFormat.prec:ℤ)+1 from by ring,
            zpow_add₀ h2ne, zpow_one]
      rw [h1, mul_div_cancel_right₀ _ h2ne, ← zpow_add₀ h2ne]
      congr 1; ring
    -- 2 * 2^max_exp = 2^(max_exp+1)
    have hfirst : (2:R) * (2:R)^FloatFormat.max_exp = (2:R)^(FloatFormat.max_exp+1) := by
      rw [show (FloatFormat.max_exp:ℤ)+1 = 1+FloatFormat.max_exp from by ring,
          zpow_add₀ h2ne, zpow_one]
    calc (2 - (2:R)^(1-(FloatFormat.prec:ℤ))/2) * (2:R)^FloatFormat.max_exp
        = 2 * (2:R)^FloatFormat.max_exp -
          (2:R)^(1-(FloatFormat.prec:ℤ))/2 * (2:R)^FloatFormat.max_exp := by ring
      _ = (2:R)^(FloatFormat.max_exp+1) - (2:R)^(FloatFormat.max_exp-FloatFormat.prec) := by
          rw [hterm, hfirst]
      _ = (2:R)^(a+e_base) - (2:R)^(b+e_base) := by congr 1 <;> congr 1 <;> omega
      _ = ((2:R)^a - (2:R)^b) * (2:R)^e_base := by
          rw [zpow_add₀ h2ne, zpow_add₀ h2ne]; ring
  -- From hlo and hhi, derive n-1 < 2^a - 2^b < n+1.
  rw [hOT_factored] at hlo hhi
  have h_cancel_lo := lt_of_mul_lt_mul_right hlo hE_pos.le
  have h_cancel_hi := lt_of_mul_lt_mul_right hhi hE_pos.le
  -- Now: (↑↑n - 1 : R) < 2^a - 2^b and 2^a - 2^b < (↑↑n + 1 : R)
  -- Case split on b
  rcases le_or_gt b 0 with hb_le | hb_gt
  · -- b ≤ 0: 0 < 2^b ≤ 1, so 2^a - 1 ≤ 2^a - 2^b < 2^a.
    -- The integer in (n-1, n+1) must be n. And n ≤ 2^a.
    -- Since a = b + prec + 1 ≤ prec + 1, 2^a ≤ 2^(prec+1).
    -- But n > 2^(prec+3) > 2^(prec+1). Contradiction.
    have ha_bound : a ≤ FloatFormat.prec + 1 := by omega
    have h2a_bound : (2 : R) ^ a ≤ (2 : R) ^ (FloatFormat.prec + 1) :=
      two_zpow_mono ha_bound
    have h2b_pos : (0 : R) < (2 : R) ^ b := zpow_pos (by norm_num) _
    -- 2^a - 2^b < 2^a ≤ 2^(prec+1)
    have hOT_E_lt : (2 : R) ^ a - (2 : R) ^ b < (2 : R) ^ (FloatFormat.prec + 1) :=
      calc (2:R) ^ a - (2:R) ^ b < (2:R) ^ a := by linarith
        _ ≤ (2:R) ^ (FloatFormat.prec + 1) := h2a_bound
    -- n > 2^(prec+3), so n+1 > 2^(prec+3) > 2^(prec+1) (for prec ≥ 1, but prec+3 ≥ prec+1)
    have hn_ge : (↑↑n - 1 : R) ≥ (2 : R) ^ (FloatFormat.prec + 1) := by
      have : 2 ^ (FloatFormat.prec.toNat + 1) ≤ 2 ^ (FloatFormat.prec.toNat + 3) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h_nat : 2 ^ (FloatFormat.prec.toNat + 1) + 1 ≤ n := by omega
      have : ((2 ^ (FloatFormat.prec.toNat + 1) + 1 : ℕ) : R) ≤ ((n : ℕ) : R) :=
        Nat.cast_le.mpr h_nat
      rw [show (FloatFormat.prec : ℤ) + 1 = ((FloatFormat.prec.toNat + 1 : ℕ) : ℤ) from by
            have := FloatFormat.valid_prec; omega,
          zpow_natCast]
      push_cast at this ⊢; linarith
    simp only [Int.cast_natCast] at h_cancel_lo
    linarith
  · -- b ≥ 1: 2^a and 2^b are both even integers (a ≥ b+prec+1 ≥ prec+2 ≥ 2, b ≥ 1).
    -- So 2^a - 2^b is an even integer. The only integer in (n-1,n+1) is n (odd). Contradiction.
    have ha_ge : 2 ≤ a := by have := FloatFormat.valid_prec; omega
    -- Cast to ℤ: n-1 < 2^a - 2^b < n+1, so 2^a - 2^b = n.
    have hb_nat : 0 < b.toNat := by omega
    have ha_nat : 0 < a.toNat := by omega
    -- Express in ℤ via cast
    have h_cast : (2 : R) ^ a - (2 : R) ^ b = ((2 ^ a.toNat - 2 ^ b.toNat : ℤ) : R) := by
      have ha' : a = (a.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
      have hb' : b = (b.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
      rw [ha', hb', zpow_natCast, zpow_natCast]; norm_cast
    rw [h_cast] at h_cancel_lo h_cancel_hi
    have h1 : ((n : ℤ) - 1) < (2 ^ a.toNat - 2 ^ b.toNat : ℤ) := by exact_mod_cast h_cancel_lo
    have h2 : (2 ^ a.toNat - 2 ^ b.toNat : ℤ) < ((n : ℤ) + 1) := by exact_mod_cast h_cancel_hi
    have h_eq : (2 ^ a.toNat - 2 ^ b.toNat : ℤ) = n := by omega
    -- 2^a and 2^b are both even, so 2^a - 2^b is even.
    have h_even : 2 ∣ (2 ^ a.toNat - 2 ^ b.toNat : ℤ) := by
      have ha2 : (2 : ℤ) ∣ 2 ^ a.toNat := dvd_pow_self 2 (by omega)
      have hb2 : (2 : ℤ) ∣ 2 ^ b.toNat := dvd_pow_self 2 (by omega)
      exact Int.dvd_sub ha2 hb2
    rw [h_eq] at h_even
    -- n is odd, contradiction
    have : ¬(2 ∣ (n : ℤ)) := by omega
    exact absurd h_even this

/-- When the predecessor has `m = 0` (so toVal = 0), the midpoint `succ_fp.toVal / 2`
    is outside the odd interval `((n-1)*E, (n+1)*E)` for odd `n > 2^(prec+3)`.

    Parity argument: writing `succ_fp.toVal / 2 = m * 2^d * E`, where `d = e - prec - e_base`:
    - `d ≤ 0`: `m * 2^d ≤ m < 2^prec < n-1`, so midpoint `≤ (n-1)*E`
    - `d = 1`: `m * 2 = n` forces `n < 2 * 2^prec`, contradicting `n > 2^(prec+3)`
    - `d ≥ 2`: `m * 2^d` is even, but `n` is odd -/
theorem midpoint_zero_pred_outside_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ} {succ_fp : FiniteFp}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hsucc_s : succ_fp.s = false) :
    (succ_fp.toVal : R) / 2 ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base ∨
    ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R) / 2 := by
  set d := succ_fp.e - FloatFormat.prec - e_base with hd_def
  have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  have hE_ne : (2 : R) ^ e_base ≠ 0 := ne_of_gt hE_pos
  have hsucc_toVal : (succ_fp.toVal : R) = ↑succ_fp.m * (2 : R) ^ (succ_fp.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hsucc_s]; simp
  -- Express midpoint in terms of d
  have hexp_split : succ_fp.e - FloatFormat.prec + 1 = (d + 1) + e_base := by omega
  have hmid_val : (succ_fp.toVal : R) / 2 = ↑succ_fp.m * (2 : R) ^ d * (2 : R) ^ e_base := by
    rw [hsucc_toVal, hexp_split, zpow_add₀ (by norm_num : (2:R) ≠ 0),
        zpow_add₀ (by norm_num : (2:R) ≠ 0)]
    simp only [zpow_one]; ring
  -- Show midpoint is outside the interval by contradiction
  by_contra h_in; push_neg at h_in
  -- h_in: (n-1)*E < midpoint < (n+1)*E
  -- i.e., (n-1)*E < m * 2^d * E < (n+1)*E, so n-1 < m * 2^d < n+1
  have h_cancel : (↑↑n - 1 : R) < ↑succ_fp.m * (2 : R) ^ d ∧
      ↑succ_fp.m * (2 : R) ^ d < (↑↑n + 1 : R) := by
    constructor
    · have h := h_in.1; rw [hmid_val] at h
      have := lt_of_mul_lt_mul_right h hE_pos.le
      exact_mod_cast this
    · have h := h_in.2; rw [hmid_val] at h
      have := lt_of_mul_lt_mul_right h hE_pos.le
      exact_mod_cast this
  have hm_bound : succ_fp.m < 2 ^ FloatFormat.prec.toNat := succ_fp.valid.2.2.1
  rcases le_or_gt d 0 with hd_le | hd_gt
  · -- d ≤ 0: m * 2^d ≤ m < 2^prec < n-1
    have h2d_le : (2 : R) ^ d ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1:R) ≤ 2) hd_le
    have : ↑succ_fp.m * (2 : R) ^ d ≤ ↑succ_fp.m := by
      calc ↑succ_fp.m * (2:R) ^ d ≤ ↑succ_fp.m * 1 := by gcongr
        _ = ↑succ_fp.m := mul_one _
    have : (↑succ_fp.m : R) < (↑↑n - 1 : R) := by
      have : (succ_fp.m : R) < (2 : R) ^ (FloatFormat.prec.toNat : ℤ) := by
        rw [zpow_natCast]; exact_mod_cast hm_bound
      have : (2 : R) ^ (FloatFormat.prec.toNat : ℤ) ≤ (↑↑n - 1 : R) := by
        rw [zpow_natCast]
        have h_nat : 2 ^ FloatFormat.prec.toNat + 1 ≤ n := by
          have := Nat.pow_le_pow_right (show 0 < 2 by omega)
              (show FloatFormat.prec.toNat ≤ FloatFormat.prec.toNat + 3 by omega)
          omega
        have : ((2 ^ FloatFormat.prec.toNat + 1 : ℕ) : R) ≤ ((n : ℕ) : R) :=
          Nat.cast_le.mpr h_nat
        push_cast at this ⊢; linarith
      linarith
    linarith
  · -- d ≥ 1
    rcases eq_or_lt_of_le (show 1 ≤ d from hd_gt) with hd_eq | hd_ge2
    · -- d = 1: m * 2^1 = m * 2. For this to be in (n-1,n+1), m*2 = n.
      -- But m < 2^prec and n > 2^(prec+3).
      rw [← hd_eq] at h_cancel
      simp only [zpow_one] at h_cancel
      have hm2_eq_n : succ_fp.m * 2 = n := by
        have h1 : ((n : ℤ) - 1 : ℤ) < (succ_fp.m : ℤ) * 2 := by exact_mod_cast h_cancel.1
        have h2 : (succ_fp.m : ℤ) * 2 < (n : ℤ) + 1 := by exact_mod_cast h_cancel.2
        omega
      omega
    · -- d ≥ 2: m * 2^d is even, n is odd
      have h_even : 2 ∣ (succ_fp.m * 2 ^ d.toNat) := by
        exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
      have h_cast : (↑succ_fp.m : R) * (2 : R) ^ d = ↑(succ_fp.m * 2 ^ d.toNat) := by
        rw [show d = (d.toNat : ℤ) from (Int.toNat_of_nonneg (by omega : 0 ≤ d)).symm,
            zpow_natCast]; norm_cast
      rw [h_cast] at h_cancel
      have h_nat_eq : succ_fp.m * 2 ^ d.toNat = n := by
        have h1 : ((n : ℤ) - 1 : ℤ) < ↑(succ_fp.m * 2 ^ d.toNat) := by exact_mod_cast h_cancel.1
        have h2 : ↑(succ_fp.m * 2 ^ d.toNat) < (n : ℤ) + 1 := by exact_mod_cast h_cancel.2
        omega
      exact absurd h_nat_eq (by omega)

/-! ## Parity and Constancy on Odd Intervals

The key parity argument: no representable float lies strictly inside `((n-1)*E, (n+1)*E)`
when `n` is odd and `n > 2^prec`. Combined with monotonicity and idempotence, this gives
constancy of all rounding modes on such intervals. -/

-- BEGIN EXTRACTED FROM Div.lean --

/-- No positive representable float has toVal in the open interval
    `((n-1) * 2^e_base, (n+1) * 2^e_base)` when `n` is odd and `n > 2^prec`.

    This is the key parity lemma: representable values `m * 2^d` satisfy
    - d ≥ 1: `m * 2^d` is even, `n` is odd → parity mismatch
    - d = 0: `m < 2^prec < n` → too small
    - d ≤ -1: `m * 2^d < 2^(prec-1) < n - 1` → below the interval -/
theorem no_representable_in_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ FloatFormat.prec.toNat < n)
    (f : FiniteFp) (hfs : f.s = false) (hfm : 0 < f.m) :
    ¬(((n : ℤ) - 1 : R) * (2 : R) ^ e_base < (f.toVal : R) ∧
      (f.toVal : R) < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base) := by
  intro ⟨hlo, hhi⟩
  -- Unfold toVal for positive float: f.toVal = f.m * 2^(f.e - prec + 1)
  have htoVal : (f.toVal : R) = ↑f.m * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hfs]; simp
  rw [htoVal] at hlo hhi
  -- Factor: f.e - prec + 1 = e_base + d
  set d := f.e - FloatFormat.prec + 1 - e_base with hd_def
  have hexp_eq : f.e - FloatFormat.prec + 1 = e_base + d := by omega
  rw [hexp_eq, zpow_add₀ (by norm_num : (2:R) ≠ 0)] at hlo hhi
  -- Divide by 2^e_base (positive) to reduce to: f.m * 2^d ∈ (n-1, n+1)
  have hE : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0:R) < 2) _
  -- Factor out 2^e_base from both inequalities
  rw [show ↑f.m * ((2:R)^e_base * (2:R)^d) = ↑f.m * (2:R)^d * (2:R)^e_base from by ring] at hlo hhi
  have hlo' : ((n : ℤ) - 1 : R) < ↑f.m * (2 : R) ^ d := by
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_right h (le_of_lt hE)]
  have hhi' : (↑f.m : R) * (2 : R) ^ d < ((n : ℤ) + 1 : R) := by
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_right h (le_of_lt hE)]
  -- Key bound
  have hm_bound : f.m < 2 ^ FloatFormat.prec.toNat := f.valid.2.2.1
  rcases le_or_gt d 0 with hd_le | hd_pos
  · -- d ≤ 0: f.m * 2^d ≤ f.m ≤ n - 1, contradicting hlo'
    have h1 : (↑f.m : R) * (2 : R) ^ d ≤ ↑f.m := by
      calc (↑f.m : R) * (2:R)^d ≤ ↑f.m * 1 := by
            gcongr; exact zpow_le_one_of_nonpos₀ (by norm_num : (1:R) ≤ 2) hd_le
        _ = ↑f.m := mul_one _
    have h2 : (↑f.m : R) ≤ (n : ℤ) - 1 := by
      have : f.m ≤ n - 1 := by omega
      exact_mod_cast show (f.m : ℤ) ≤ (n : ℤ) - 1 from by omega
    linarith
  · -- d ≥ 1: f.m * 2^d is even, n is odd → parity contradiction
    have hd_nat_pos : 0 < d.toNat := by omega
    -- Rewrite as natural number: f.m * 2^d = ↑(f.m * 2^d.toNat)
    have hfm_2d : (↑f.m : R) * (2 : R) ^ d = ↑(f.m * 2 ^ d.toNat) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast (2 : R) d.toNat,
          Int.toNat_of_nonneg (by omega : 0 ≤ d)]
    rw [hfm_2d] at hlo' hhi'
    -- f.m * 2^d.toNat is even (since d.toNat ≥ 1)
    have heven : 2 ∣ f.m * 2 ^ d.toNat := by
      exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
    -- f.m * 2^d ≠ n (even ≠ odd)
    have hne : f.m * 2 ^ d.toNat ≠ n := by
      intro heq
      have : 2 ∣ n := heq ▸ heven
      obtain ⟨k, hk⟩ := this; omega
    -- Pull back to integer arithmetic
    have hlo_int : (n : ℤ) - 1 < ↑(f.m * 2 ^ d.toNat) := by exact_mod_cast hlo'
    have hhi_int : (↑(f.m * 2 ^ d.toNat) : ℤ) < ↑n + 1 := by exact_mod_cast hhi'
    -- The only integer in (n-1, n+1) is n
    exact hne (by omega)

/-- A power of 2 is representable as a FiniteFp when the exponent is in range. -/
private theorem exists_representable_pow2 {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (e : ℤ) (he_min : FloatFormat.min_exp ≤ e) (he_max : e ≤ FloatFormat.max_exp) :
    ∃ f : FiniteFp, f.s = false ∧ 0 < f.m ∧
      (f.toVal : R) = (2 : R) ^ e := by
  set p := FloatFormat.prec.toNat with hp_def
  have hp_ge : 2 ≤ p := by have := FloatFormat.valid_prec; omega
  -- Construct: m = 2^(p-1), exponent = e
  -- toVal = sign' * m * 2^(e - prec + 1) = 1 * 2^(p-1) * 2^(e - prec + 1) = 2^(e + p - 1 - prec + 1) = 2^e
  -- since p = prec.toNat and prec ≥ 2
  refine ⟨⟨false, e, 2 ^ (p - 1), ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · exact he_min
  · exact he_max
  · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · left; constructor
    · rw [FloatFormat.prec_sub_one_toNat_eq_toNat_sub, hp_def]
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · exact Nat.pos_of_ne_zero (by positivity)
  · unfold FiniteFp.toVal FiniteFp.sign'; simp [FloatFormat.radix_val_eq_two]
    rw [← zpow_natCast (2 : R) (p - 1), ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]
    congr 1
    have : (FloatFormat.prec - 1).toNat = p - 1 := by
      rw [hp_def]; exact FloatFormat.prec_sub_one_toNat_eq_toNat_sub
    omega

/-- The midpoint of two representable floats bounding an odd interval lies outside
    the interval `((n-1)*E, (n+1)*E)`. -/
private theorem midpoint_outside_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (pred_fp succ_fp : FiniteFp)
    (hps : pred_fp.s = false) (hpm : 0 < pred_fp.m)
    (hss : succ_fp.s = false) (hsm : 0 < succ_fp.m)
    (hpred_le : (pred_fp.toVal : R) ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
    (hsucc_ge : ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R))
    (hgap : ∀ g : FiniteFp, g.s = false → 0 < g.m →
      (pred_fp.toVal : R) < (g.toVal : R) → (g.toVal : R) < (succ_fp.toVal : R) → False) :
    ((pred_fp.toVal : R) + succ_fp.toVal) / 2 ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base ∨
    ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by
  set E := (2 : R) ^ e_base with hE_def
  set p := FloatFormat.prec.toNat with hp_def
  have hE_pos : (0 : R) < E := zpow_pos (by norm_num : (0:R) < 2) _
  have hE_ne : E ≠ (0 : R) := ne_of_gt hE_pos
  -- Express toVals
  have hpred_toVal : (pred_fp.toVal : R) = ↑pred_fp.m * (2 : R) ^ (pred_fp.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hps]; simp
  have hsucc_toVal : (succ_fp.toVal : R) = ↑succ_fp.m * (2 : R) ^ (succ_fp.e - FloatFormat.prec + 1) := by
    unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hss]; simp
  -- d_s ≥ 0: succ.toVal ≥ (n+1)*E > 2^(p+3)*E, so e_s - p + 1 > e_base
  set d_s := succ_fp.e - FloatFormat.prec + 1 - e_base with hd_s_def
  have hd_s_nonneg : 0 ≤ d_s := by
    by_contra hd_neg; push_neg at hd_neg
    have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
    have hexp_lt : succ_fp.e - FloatFormat.prec + 1 < e_base := by omega
    -- succ.toVal < m_s * E (since 2^(e_s-p+1) < 2^e_base = E)
    have h_succ_lt : (succ_fp.toVal : R) < ↑succ_fp.m * E := by
      rw [hsucc_toVal, hE_def]
      have hsm_R : (0 : R) < ↑succ_fp.m := by exact_mod_cast hsm
      have hzpow : (2 : R) ^ (succ_fp.e - FloatFormat.prec + 1) < (2:R) ^ e_base :=
        zpow_lt_zpow_right₀ (by norm_num : (1:R) < 2) hexp_lt
      exact mul_lt_mul_of_pos_left hzpow hsm_R
    -- m_s < 2^p, so succ < 2^p * E
    have h_ms_cast : (↑succ_fp.m : R) < (2 : R) ^ (p : ℤ) := by
      rw [zpow_natCast]; exact_mod_cast hm_s
    have h_succ_lt2 : (succ_fp.toVal : R) < (2 : R) ^ (p : ℤ) * E := by
      calc (succ_fp.toVal : R) < ↑succ_fp.m * E := h_succ_lt
        _ < (2:R) ^ (p : ℤ) * E := by exact mul_lt_mul_of_pos_right h_ms_cast hE_pos
    -- But (n+1)*E ≤ succ and 2^p ≤ n+1
    have hp_le_n : 2 ^ p ≤ n := by
      have : 2 ^ p ≤ 2 ^ (p + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hn_cast : (2 : R) ^ (p : ℤ) ≤ ((n : ℤ) + 1 : R) := by
      rw [zpow_natCast]; push_cast; exact_mod_cast Nat.le_succ_of_le hp_le_n
    linarith [mul_le_mul_of_nonneg_right hn_cast (le_of_lt hE_pos)]
  -- d_p ≥ 0: if d_p < 0, pred < 2^p * E but succ > 2^(p+3) * E, so there's a
  -- representable power of 2 between them, contradicting hgap.
  set d_p := pred_fp.e - FloatFormat.prec + 1 - e_base with hd_p_def
  have hd_p_nonneg : 0 ≤ d_p := by
    by_contra hd_neg; push_neg at hd_neg
    have hm_p : pred_fp.m < 2 ^ p := pred_fp.valid.2.2.1
    have hexp_lt_p : pred_fp.e - FloatFormat.prec + 1 < e_base := by omega
    -- pred < 2^p * E
    have hpred_lt : (pred_fp.toVal : R) < (2 : R) ^ (p : ℤ) * E := by
      rw [hpred_toVal, hE_def]
      have hpm_R : (0 : R) < ↑pred_fp.m := by exact_mod_cast hpm
      have hzpow_lt : (2:R) ^ (pred_fp.e - FloatFormat.prec + 1) < (2:R) ^ e_base :=
        zpow_lt_zpow_right₀ (by norm_num : (1:R) < 2) hexp_lt_p
      have hm_le : (↑pred_fp.m : R) ≤ (2:R) ^ (p:ℤ) := by
        rw [zpow_natCast]; exact_mod_cast Nat.le_of_lt hm_p
      calc ↑pred_fp.m * (2:R) ^ (pred_fp.e - FloatFormat.prec + 1)
          < ↑pred_fp.m * (2:R) ^ e_base := mul_lt_mul_of_pos_left hzpow_lt hpm_R
        _ ≤ (2:R) ^ (p:ℤ) * (2:R) ^ e_base := mul_le_mul_of_nonneg_right hm_le (le_of_lt (zpow_pos (by norm_num : (0:R) < 2) _))
    -- Consider the power of 2 at e_base + p (between pred and succ)
    have he_valid_min : FloatFormat.min_exp ≤ e_base + (p : ℤ) := by
      have := pred_fp.valid.1; omega
    have he_valid_max : e_base + (p : ℤ) ≤ FloatFormat.max_exp := by
      -- From d_s ≥ 0 and succ ≥ (n+1)*E > 2^(p+3)*E, succ_fp.e > p + 2 + e_base
      -- So max_exp ≥ succ_fp.e > p + e_base
      have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
      have hds_exp : succ_fp.e - FloatFormat.prec + 1 ≥ e_base := by omega
      -- succ = m_s * 2^(d_s + e_base) with d_s ≥ 0
      -- succ ≥ (n+1)*E > 2^(p+3)*E, and m_s < 2^p
      -- so 2^(d_s + e_base) > 2^(p+3+e_base) / 2^p = 2^(3+e_base), i.e., d_s > 3
      -- and succ_fp.e = d_s + prec - 1 + e_base ≥ 4 + prec - 1 + e_base = prec + 3 + e_base
      -- max_exp ≥ succ_fp.e ≥ prec + 3 + e_base > p + e_base
      have := succ_fp.valid.2.1
      -- We just need max_exp ≥ e_base + p, i.e., succ_fp.e ≥ e_base + p
      -- succ_fp.e ≥ e_base + prec - 1 ≥ e_base + p - 1 (not enough, need ≥ e_base + p)
      -- Use: if succ_fp.e = e_base + prec - 1, then d_s = 0, succ = m_s * E,
      -- but m_s < 2^p < n+1, contradicting succ ≥ (n+1)*E
      by_contra h; push_neg at h
      -- succ_fp.e < e_base + p, combined with d_s ≥ 0 (succ_fp.e ≥ e_base + prec - 1)
      -- gives succ_fp.e - prec + 1 = e_base (since d_s = 0)
      have hd_s_eq : d_s = 0 := by
        have : succ_fp.e ≤ e_base + (p : ℤ) - 1 := by omega
        have : d_s ≤ 0 := by
          simp only [hd_s_def, hp_def] at *
          have hprec_eq : FloatFormat.prec = (FloatFormat.prec.toNat : ℤ) :=
            (Int.toNat_of_nonneg (by have := FloatFormat.valid_prec; omega)).symm
          omega
        omega
      -- So succ.toVal = m_s * E
      have hexp_eq : succ_fp.e - FloatFormat.prec + 1 = e_base := by
        simp only [hd_s_def] at hd_s_eq
        omega
      have hsucc_eq : (succ_fp.toVal : R) = ↑succ_fp.m * E := by
        rw [hsucc_toVal, hE_def, hexp_eq]
      -- m_s ≥ n+1 from succ ≥ (n+1)*E
      have hms_ge : (n : ℤ) + 1 ≤ succ_fp.m := by
        have h1 : ((n : ℤ) + 1 : R) * E ≤ ↑succ_fp.m * E := by rw [← hsucc_eq]; exact hsucc_ge
        exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
      -- But m_s < 2^p ≤ n < n+1
      have hp_le_n : 2 ^ p ≤ n := Nat.le_of_lt (lt_of_le_of_lt
        (Nat.pow_le_pow_right (by omega) (by omega : p ≤ p + 3)) hn_large)
      have : succ_fp.m < n + 1 := lt_of_lt_of_le hm_s (Nat.le_succ_of_le hp_le_n)
      exact absurd hms_ge (by exact_mod_cast not_le.mpr this)
    obtain ⟨g, hgs, hgm, hgval⟩ := exists_representable_pow2 (R := R) (e_base + p) he_valid_min he_valid_max
    -- g.toVal = 2^(e_base + p) = 2^p * E
    have hg_eq : (g.toVal : R) = (2:R) ^ (p:ℤ) * E := by
      rw [hgval, hE_def, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; ring_nf
    -- pred < g < succ
    have hg_gt_pred : (pred_fp.toVal : R) < g.toVal := by rw [hg_eq]; exact hpred_lt
    have hg_lt_succ : (g.toVal : R) < succ_fp.toVal := by
      rw [hg_eq]
      calc (2:R) ^ (p:ℤ) * E < ((n : ℤ) + 1 : R) * E := by
            gcongr
            rw [zpow_natCast]; push_cast; exact_mod_cast Nat.le_succ_of_le (by
              have : 2 ^ p ≤ 2 ^ (p+3) := Nat.pow_le_pow_right (by omega) (by omega); omega)
        _ ≤ succ_fp.toVal := hsucc_ge
    exact hgap g hgs hgm hg_gt_pred hg_lt_succ
  -- Now express toVals as k * E with 16 | k
  -- pred.toVal = m_p * 2^(e_p - prec + 1) = m_p * 2^(d_p + e_base) = (m_p * 2^d_p) * E
  set k_p := pred_fp.m * 2 ^ d_p.toNat with hk_p_def
  set k_s := succ_fp.m * 2 ^ d_s.toNat with hk_s_def
  have hpred_eq : (pred_fp.toVal : R) = (k_p : R) * E := by
    rw [hpred_toVal, hE_def, hk_p_def]
    push_cast
    -- Goal: m * 2^(e-p+1) = m * 2^d_p.toNat * 2^e_base
    have h2ne : (2:R) ≠ 0 := by norm_num
    have hexp : pred_fp.e - FloatFormat.prec + 1 = ↑d_p.toNat + e_base := by
      have : (d_p.toNat : ℤ) = d_p := Int.toNat_of_nonneg hd_p_nonneg; omega
    rw [hexp, zpow_add₀ h2ne, zpow_natCast]; ring
  have hsucc_eq : (succ_fp.toVal : R) = (k_s : R) * E := by
    rw [hsucc_toVal, hE_def, hk_s_def]
    push_cast
    have h2ne : (2:R) ≠ 0 := by norm_num
    have hexp : succ_fp.e - FloatFormat.prec + 1 = ↑d_s.toNat + e_base := by
      have : (d_s.toNat : ℤ) = d_s := Int.toNat_of_nonneg hd_s_nonneg; omega
    rw [hexp, zpow_add₀ h2ne, zpow_natCast]; ring
  -- d_s ≥ 4: from succ ≥ (n+1)*E > 2^(p+3)*E and m_s < 2^p
  have hd_s_ge4 : 4 ≤ d_s.toNat := by
    by_contra hd_lt; push_neg at hd_lt
    have hm_s : succ_fp.m < 2 ^ p := succ_fp.valid.2.2.1
    -- k_s = m_s * 2^d_s < 2^p * 2^3 = 2^(p+3) ≤ n < n+1
    have hks_lt : k_s < 2 ^ (p + 3) := by
      rw [hk_s_def]
      calc succ_fp.m * 2 ^ d_s.toNat
          < 2 ^ p * 2 ^ d_s.toNat := by
            exact (Nat.mul_lt_mul_right (by positivity)).mpr hm_s
        _ ≤ 2 ^ p * 2 ^ 3 := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ = 2 ^ (p + 3) := by rw [← Nat.pow_add]
    -- But k_s * E ≥ (n+1)*E, so k_s ≥ n+1 > 2^(p+3)
    have hks_ge : n + 1 ≤ k_s := by
      have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
      exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
    omega
  -- d_p ≥ 2: if d_p < 2, pred < 2^(p+1)*E, use rep value at 2^(e_base+p+1) for contradiction
  have hd_p_ge2 : 2 ≤ d_p.toNat := by
    by_contra hd_lt; push_neg at hd_lt
    have hm_p : pred_fp.m < 2 ^ p := pred_fp.valid.2.2.1
    have hkp_lt : k_p < 2 ^ (p + 1) := by
      rw [hk_p_def]
      calc pred_fp.m * 2 ^ d_p.toNat
          < 2 ^ p * 2 ^ d_p.toNat := by
            exact (Nat.mul_lt_mul_right (by positivity)).mpr hm_p
        _ ≤ 2 ^ p * 2 ^ 1 := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ = 2 ^ (p + 1) := by rw [← Nat.pow_add]
    have hpred_lt : (pred_fp.toVal : R) < (2:R) ^ (e_base + (p : ℤ) + 1) := by
      rw [hpred_eq, hE_def]
      have hkp_R : (k_p : R) < (2:R) ^ (p + 1 : ℕ) := by exact_mod_cast hkp_lt
      calc (k_p : R) * (2:R) ^ e_base
          < (2:R) ^ (p + 1 : ℕ) * (2:R) ^ e_base := by
            exact mul_lt_mul_of_pos_right hkp_R (zpow_pos (by norm_num : (0:R) < 2) e_base)
        _ = (2:R) ^ (e_base + (p : ℤ) + 1) := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; congr 1; push_cast; ring
    -- Representable value at 2^(e_base + p + 1)
    have he2_max : e_base + (p : ℤ) + 1 ≤ FloatFormat.max_exp := by
      have := succ_fp.valid.2.1
      have : (d_s.toNat : ℤ) ≥ 4 := by exact_mod_cast hd_s_ge4
      have : (d_s.toNat : ℤ) = d_s := Int.toNat_of_nonneg hd_s_nonneg
      have hp_int : (p : ℤ) = FloatFormat.prec := by
        rw [hp_def]; exact Int.toNat_of_nonneg (by linarith [FloatFormat.valid_prec])
      omega
    have he2_min : FloatFormat.min_exp ≤ e_base + (p : ℤ) + 1 := by
      have := pred_fp.valid.1; omega
    obtain ⟨g, hgs, hgm, hgval⟩ := exists_representable_pow2 (R := R) (e_base + p + 1) he2_min he2_max
    have hg_gt : (pred_fp.toVal : R) < g.toVal := by rw [hgval]; exact hpred_lt
    have hg_lt : (g.toVal : R) < succ_fp.toVal := by
      rw [hgval, hsucc_eq, hE_def]
      have hks_large : 2 ^ (p + 1) < k_s := by
        have : n + 1 ≤ k_s := by
          have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
          exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
        have : 2 ^ (p + 1) ≤ n := by
          have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show p + 1 ≤ p + 3 by omega)
          omega
        omega
      calc (2:R) ^ (e_base + (p : ℤ) + 1)
          = (2:R) ^ (p + 1 : ℕ) * (2:R) ^ e_base := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:R) ≠ 0)]; congr 1; push_cast; ring
        _ < (k_s : R) * (2:R) ^ e_base := by
            apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num : (0:R) < 2) e_base)
            exact_mod_cast hks_large
    exact hgap g hgs hgm hg_gt hg_lt
  -- Now 4 | k_p and 16 | k_s
  have h4_kp : 4 ∣ k_p := by
    rw [hk_p_def]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd_p_ge2) _
  have h16_ks : 16 ∣ k_s := by
    rw [hk_s_def]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hd_s_ge4) _
  -- k_p + k_s ≡ 0 mod 4
  have h4_sum : 4 ∣ (k_p + k_s) := Nat.dvd_add h4_kp (dvd_trans (by norm_num : (4:ℕ) ∣ 16) h16_ks)
  -- 2n ≡ 2 mod 4 (n odd), so k_p + k_s ≠ 2n
  have hsum_ne : k_p + k_s ≠ 2 * n := by omega
  -- k_p ≤ n-1 and k_s ≥ n+1
  have hkp_le : k_p ≤ n - 1 := by
    have h1 : (k_p : R) * E ≤ ((n : ℤ) - 1 : R) * E := by rw [← hpred_eq]; exact hpred_le
    have h2 : (k_p : R) ≤ ((n : ℤ) - 1 : R) := le_of_mul_le_mul_right h1 hE_pos
    have hn_ge : 1 ≤ n := by omega
    have : (k_p : ℤ) ≤ (n : ℤ) - 1 := by exact_mod_cast h2
    omega
  have hks_ge : n + 1 ≤ k_s := by
    have h1 : ((n : ℤ) + 1 : R) * E ≤ (k_s : R) * E := by rw [← hsucc_eq]; exact hsucc_ge
    exact_mod_cast le_of_mul_le_mul_right h1 hE_pos
  -- k_p + k_s ≤ 2(n-1) or k_p + k_s ≥ 2(n+1)
  have hsum_bound : k_p + k_s ≤ 2 * n - 2 ∨ 2 * n + 2 ≤ k_p + k_s := by omega
  -- Convert to R
  rcases hsum_bound with h | h
  · left
    rw [hpred_eq, hsucc_eq]
    have : ((k_p + k_s : ℕ) : R) ≤ (2 * n - 2 : ℕ) := by exact_mod_cast h
    have h2le : 2 ≤ 2 * n := by omega
    have hcast : ((2 * n - 2 : ℕ) : R) = 2 * (((n : ℤ) - 1 : R)) := by
      rw [Nat.cast_sub h2le]; push_cast; ring
    calc ((k_p : R) * E + (k_s : R) * E) / 2
        = ((k_p + k_s : ℕ) : R) * E / 2 := by push_cast; ring
      _ ≤ ((2 * n - 2 : ℕ) : R) * E / 2 := by gcongr
      _ = (((n : ℤ) - 1 : R)) * E := by rw [hcast]; ring
  · right
    rw [hpred_eq, hsucc_eq]
    have : (2 * n + 2 : ℕ) ≤ ((k_p + k_s : ℕ) : R) := by exact_mod_cast h
    have hcast : ((2 * n + 2 : ℕ) : R) = 2 * (((n : ℤ) + 1 : R)) := by push_cast; ring
    calc (((n : ℤ) + 1 : R)) * E
        = ((2 * n + 2 : ℕ) : R) * E / 2 := by rw [hcast]; ring
      _ ≤ ((k_p + k_s : ℕ) : R) * E / 2 := by gcongr
      _ = ((k_p : R) * E + (k_s : R) * E) / 2 := by push_cast; ring

/-- No positive representable float has `toVal` strictly inside `(lo, hi)`. -/
abbrev noRepresentableIn [FloatFormat] {R : Type*} [Field R] [LT R] (lo hi : R) : Prop :=
  ∀ f : FiniteFp, f.s = false → 0 < f.m → ¬(lo < (f.toVal : R) ∧ (f.toVal : R) < hi)

/-- Lower endpoint of the odd interval `((n-1)*2^e_base, (n+1)*2^e_base)`. -/
abbrev oddIntervalLo [FloatFormat] {R : Type*} [Field R] (n : ℕ) (e_base : ℤ) : R :=
  ((n : ℤ) - 1 : R) * (2 : R) ^ e_base

/-- Upper endpoint of the odd interval `((n-1)*2^e_base, (n+1)*2^e_base)`. -/
abbrev oddIntervalHi [FloatFormat] {R : Type*} [Field R] (n : ℕ) (e_base : ℤ) : R :=
  ((n : ℤ) + 1 : R) * (2 : R) ^ e_base

/-- Membership in the odd interval `((n-1)*2^e_base, (n+1)*2^e_base)`. -/
abbrev inOddInterval [FloatFormat] {R : Type*} [Field R] [LT R]
    (n : ℕ) (e_base : ℤ) (v : R) : Prop :=
  oddIntervalLo (R := R) n e_base < v ∧ v < oddIntervalHi (R := R) n e_base

/-- `roundDown` is constant on positive open intervals containing no representable float.

    If no positive representable float has `toVal` in `(lo, hi)`, then `roundDown v₁ = roundDown v₂`
    for any `v₁, v₂ ∈ (lo, hi)`. Uses monotonicity + idempotence for the maximality argument. -/
theorem roundDown_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundDown v₁ = roundDown v₂ := by
  wlog hle : v₁ ≤ v₂ with H
  · exact (H hlo_pos hno_rep hv₂_lo hv₂_hi hv₁_lo hv₁_hi (le_of_lt (not_le.mp hle))).symm
  have hmono := roundDown_mono hle
  by_contra hne
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  have hrd₂ : roundDown v₂ = Fp.finite (findPredecessorPos v₂ hv₂_pos) := by
    unfold roundDown; exact findPredecessor_pos_eq v₂ hv₂_pos
  set g := findPredecessorPos v₂ hv₂_pos
  have hg_le : (g.toVal : R) ≤ v₂ := findPredecessorPos_le v₂ hv₂_pos
  have hgs : g.s = false := findPredecessorPos_sign_false v₂ hv₂_pos
  rcases le_or_gt (g.toVal : R) v₁ with hg_le_v₁ | hg_gt_v₁
  · -- g.toVal ≤ v₁: idempotent + mono gives roundDown(v₂) ≤ roundDown(v₁)
    have hidem := roundDown_idempotent (R := R) g (Or.inl hgs)
    have hge : roundDown v₂ ≤ roundDown v₁ := by
      rw [hrd₂, ← hidem]; exact roundDown_mono hg_le_v₁
    exact hne (Fp.le_antisymm hmono hge)
  · -- g.toVal > v₁ > lo: representable in (lo, hi)
    have hgm : 0 < g.m := by
      by_contra h; push_neg at h
      have : g.m = 0 := by omega
      have : (g.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith [lt_trans hlo_pos hv₁_lo]
    exact absurd ⟨lt_trans hv₁_lo hg_gt_v₁, lt_of_le_of_lt hg_le hv₂_hi⟩ (hno_rep g hgs hgm)

/-- `roundUp` is constant on positive open intervals containing no representable float. -/
theorem roundUp_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundUp v₁ = roundUp v₂ := by
  wlog hle : v₁ ≤ v₂ with H
  · exact (H hlo_pos hno_rep hv₂_lo hv₂_hi hv₁_lo hv₁_hi (le_of_lt (not_le.mp hle))).symm
  have hmono := roundUp_mono hle
  by_contra hne
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  -- Unfold roundUp v₁ to findSuccessorPos
  rw [show roundUp v₁ = findSuccessorPos v₁ hv₁_pos from by
    unfold roundUp; exact findSuccessor_pos_eq v₁ hv₁_pos] at hmono hne
  rcases hfsp : findSuccessorPos v₁ hv₁_pos with g | b | _
  · -- Case: Fp.finite g — successor is a finite float
    rw [hfsp] at hmono hne
    have hg_ge : v₁ ≤ (g.toVal : R) := findSuccessorPos_ge v₁ hv₁_pos g hfsp
    have hg_pos : (0 : R) < g.toVal := lt_of_lt_of_le hv₁_pos hg_ge
    have hgm : 0 < g.m := by
      by_contra h; push_neg at h
      have : g.m = 0 := by omega
      have : (g.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith
    have hgs : g.s = false := by
      by_contra hs
      have hs_t : g.s = true := by revert hs; cases g.s <;> simp
      have : (g.toVal : R) ≤ 0 := by
        unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hs_t]; simp
        exact mul_nonneg (by positivity) (zpow_pos (by norm_num : (0:R) < 2) _).le
      linarith
    rcases le_or_gt (g.toVal : R) v₂ with hg_le | hg_gt
    · -- g.toVal ≤ v₂: g is representable in (lo, hi)
      exact absurd ⟨lt_of_lt_of_le hv₁_lo hg_ge, lt_of_le_of_lt hg_le hv₂_hi⟩
        (hno_rep g hgs hgm)
    · -- g.toVal > v₂: roundUp(v₂) ≤ g = roundUp(v₁)
      have hidem := roundUp_idempotent (R := R) g (Or.inl hgs)
      have hge : roundUp v₂ ≤ Fp.finite g := by
        rw [← hidem]; exact roundUp_mono (le_of_lt hg_gt)
      exact hne (Fp.le_antisymm hmono hge)
  · -- Case: Fp.infinite b — overflow
    rw [hfsp] at hmono hne
    cases b with
    | true => exact absurd hfsp (findSuccessorPos_ne_neg_inf v₁ hv₁_pos)
    | false =>
      -- roundUp v₁ = +∞, hmono: +∞ ≤ roundUp v₂
      -- Everything ≤ +∞, so Fp.le_antisymm gives equality
      have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
      have hge : roundUp v₂ ≤ Fp.infinite false := by
        rw [show roundUp v₂ = findSuccessorPos v₂ hv₂_pos from by
          unfold roundUp; exact findSuccessor_pos_eq v₂ hv₂_pos]
        rcases hfsp₂ : findSuccessorPos v₂ hv₂_pos with f | c | _
        · rw [Fp.le_def]; left; simp [Fp.is_total_lt]
        · cases c with
          | false => exact Fp.le_refl _
          | true => exact absurd hfsp₂ (findSuccessorPos_ne_neg_inf v₂ hv₂_pos)
        · exact absurd hfsp₂ (findSuccessorPos_ne_nan v₂ hv₂_pos)
      exact hne (Fp.le_antisymm hmono hge)
  · -- Case: Fp.NaN — impossible for findSuccessorPos
    exact absurd hfsp (findSuccessorPos_ne_nan v₁ hv₁_pos)

/-- `roundTowardZero` is constant on positive open intervals with no representable float. -/
theorem roundTowardZero_eq_of_no_representable {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {lo hi : R} (hlo_pos : 0 < lo)
    (hno_rep : noRepresentableIn lo hi)
    {v₁ v₂ : R} (hv₁_lo : lo < v₁) (hv₁_hi : v₁ < hi) (hv₂_lo : lo < v₂) (hv₂_hi : v₂ < hi) :
    roundTowardZero v₁ = roundTowardZero v₂ := by
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  rw [roundTowardZero_pos_eq v₁ hv₁_pos, roundTowardZero_pos_eq v₂ hv₂_pos]
  exact roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi

/-- Any finite float has `toVal` strictly below the overflow threshold. -/
private theorem finite_toVal_lt_overflowThreshold {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (f : FiniteFp) :
    (f.toVal : R) < FloatFormat.overflowThreshold R :=
  calc (f.toVal : R)
      ≤ FiniteFp.largestFiniteFloat.toVal := FiniteFp.finite_le_largestFiniteFloat f
    _ < _ := largestFiniteFloat_lt_overflow_threshold

/-- If `roundUp x = Fp.finite f` for positive `x`, then `x ≤ f.toVal`. -/
private theorem le_toVal_of_roundUp_finite {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {x : R} {f : FiniteFp} (hx_pos : 0 < x) (hru : roundUp x = Fp.finite f) :
    x ≤ (f.toVal : R) := by
  rw [show roundUp x = findSuccessorPos x hx_pos from by
    unfold roundUp; exact findSuccessor_pos_eq x hx_pos] at hru
  rcases hfsp : findSuccessorPos x hx_pos with g | _ | _
  · rw [hfsp, Fp.finite.injEq] at hru; rw [← hru]
    exact findSuccessorPos_ge x hx_pos g hfsp
  · rw [hfsp] at hru; exact absurd hru (by simp)
  · exact absurd hfsp (findSuccessorPos_ne_nan x hx_pos)

/-- In an odd interval with no representable float, a crossing from roundDown to roundUp
    is impossible for any roundNearest mode. Parameterized over 4 mode-specific callbacks. -/
private theorem roundNearest_no_crossing {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {v w : R} {n : ℕ} {e_base : ℤ}
    {roundNear : R → Fp}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hv_pos : 0 < v) (hw_pos : 0 < w)
    (hv_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v)
    (hv_hi : v < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hw_hi : w < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hno_rep : noRepresentableIn (((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
        (((n : ℤ) + 1 : R) * (2 : R) ^ e_base))
    (hrd_eq : roundDown v = roundDown w)
    (hru_eq : roundUp v = roundUp w)
    (hrd_ne : roundDown v ≠ roundUp v)
    (hv_rd : roundNear v = roundDown v)
    (hw_ru : roundNear w = roundUp w)
    -- Mode-specific callbacks:
    (h_above_mid_up : ∀ (x mid_val : R) (pred succ : FiniteFp),
        0 < x → x < FloatFormat.overflowThreshold R →
        roundDown x = Fp.finite pred → roundUp x = Fp.finite succ →
        ((pred.toVal : R) + succ.toVal) / 2 = mid_val → x > mid_val →
        roundNear x = roundUp x)
    (h_below_mid_down : ∀ (x mid_val : R) (pred succ : FiniteFp),
        0 < x → x < FloatFormat.overflowThreshold R →
        roundDown x = Fp.finite pred → roundUp x = Fp.finite succ →
        ((pred.toVal : R) + succ.toVal) / 2 = mid_val → x < mid_val →
        roundNear x = roundDown x)
    (h_ge_inf : ∀ (x : R), x ≥ FloatFormat.overflowThreshold R →
        roundNear x = Fp.infinite false)
    (h_pos_succ_overflow : ∀ (x : R) (pred : FiniteFp),
        0 < x → x < FloatFormat.overflowThreshold R →
        roundDown x = Fp.finite pred → roundUp x = Fp.infinite false →
        roundNear x = Fp.finite pred) : False := by
  have hrd_v : roundDown v = Fp.finite (findPredecessorPos v hv_pos) :=
    by unfold roundDown; exact findPredecessor_pos_eq v hv_pos
  set pred_fp := findPredecessorPos v hv_pos with hpred_def
  have hpred_le_v : (pred_fp.toVal : R) ≤ v := findPredecessorPos_le v hv_pos
  have hpred_s : pred_fp.s = false := findPredecessorPos_sign_false v hv_pos
  have hru_v : roundUp v = findSuccessorPos v hv_pos :=
    by unfold roundUp; exact findSuccessor_pos_eq v hv_pos
  rw [hru_v] at hrd_ne hru_eq
  rcases hru_case : findSuccessorPos v hv_pos with succ_fp | b | _
  · -- Case 1: roundUp v = Fp.finite succ_fp
    rw [hrd_v] at hrd_ne hrd_eq
    have hsucc_ge_v : v ≤ (succ_fp.toVal : R) :=
      findSuccessorPos_ge v hv_pos succ_fp hru_case
    have hsucc_s : succ_fp.s = false := by
      by_contra hs
      have hs_t : succ_fp.s = true := by revert hs; cases succ_fp.s <;> simp
      have : (succ_fp.toVal : R) ≤ 0 := by
        unfold FiniteFp.toVal FiniteFp.sign'; rw [FloatFormat.radix_val_eq_two, hs_t]; simp
        exact mul_nonneg (by positivity) (zpow_pos (by norm_num : (0:R) < 2) _).le
      linarith
    have hsucc_m : 0 < succ_fp.m := by
      by_contra h; push_neg at h; have : succ_fp.m = 0 := by omega
      have : (succ_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [this]; simp
      linarith
    have hsucc_bound : ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤ (succ_fp.toVal : R) := by
      by_contra h; push_neg at h
      exact hno_rep succ_fp hsucc_s hsucc_m ⟨lt_of_lt_of_le hv_lo hsucc_ge_v, h⟩
    -- Threshold bounds (shared between main and degenerate cases)
    have hsucc_lt_thresh := finite_toVal_lt_overflowThreshold (R := R) succ_fp
    have hv_lt_thresh := lt_of_le_of_lt hsucc_ge_v hsucc_lt_thresh
    have hw_lt_thresh : w < FloatFormat.overflowThreshold R :=
      lt_of_le_of_lt (le_toVal_of_roundUp_finite hw_pos (hru_eq.symm.trans hru_case))
        hsucc_lt_thresh
    have hru_v_eq : roundUp v = Fp.finite succ_fp := hru_v.trans hru_case
    -- Midpoint dispatch helper: derive contradiction from hmid_outside
    suffices hmid_outside : ((pred_fp.toVal : R) + succ_fp.toVal) / 2 ≤
        ((n : ℤ) - 1 : R) * (2 : R) ^ e_base ∨
        ((n : ℤ) + 1 : R) * (2 : R) ^ e_base ≤
        ((pred_fp.toVal : R) + succ_fp.toVal) / 2 by
      rcases hmid_outside with hmid_lo | hmid_hi
      · have hv_gt_mid : v > ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have := h_above_mid_up v _ pred_fp succ_fp hv_pos hv_lt_thresh hrd_v hru_v_eq rfl hv_gt_mid
        have : roundDown v = roundUp v := hv_rd.symm.trans this
        rw [hrd_v, hru_v] at this; exact hrd_ne this
      · have hw_lt_mid : w < ((pred_fp.toVal : R) + succ_fp.toVal) / 2 := by linarith
        have := h_below_mid_down w _ pred_fp succ_fp hw_pos
          hw_lt_thresh hrd_eq.symm (hru_eq.symm.trans hru_case) rfl hw_lt_mid
        have : roundDown w = roundUp w := this.symm.trans hw_ru
        rw [← hrd_eq, ← hru_eq] at this; exact hrd_ne this
    -- Prove hmid_outside by cases on pred_fp.m
    by_cases hpred_m : 0 < pred_fp.m
    · -- Main case: pred_fp.m > 0, use midpoint_outside_odd_interval
      have hpred_bound : (pred_fp.toVal : R) ≤ ((n : ℤ) - 1 : R) * (2 : R) ^ e_base := by
        by_contra h; push_neg at h
        exact hno_rep pred_fp hpred_s hpred_m ⟨h, lt_of_le_of_lt hpred_le_v hv_hi⟩
      have hadj : ∀ g : FiniteFp, g.s = false → 0 < g.m →
          (pred_fp.toVal : R) < (g.toVal : R) → (g.toVal : R) < (succ_fp.toVal : R) → False := by
        intro g hgs hgm hg_gt_pred hg_lt_succ
        rcases le_or_gt (g.toVal : R) (((n : ℤ) - 1 : R) * (2 : R) ^ e_base) with hg_le_lo | hg_gt_lo
        · have hmono : roundDown (g.toVal : R) ≤ roundDown v :=
            roundDown_mono (le_trans (le_of_lt (lt_of_le_of_lt hg_le_lo hv_lo)) (le_refl v))
          rw [hrd_v, roundDown_idempotent (R := R) g (Or.inl hgs)] at hmono
          exact absurd hg_gt_pred (not_lt.mpr (FiniteFp.le_toVal_le R
            ((Fp.finite_le_finite_iff g pred_fp).mp hmono)))
        · rcases lt_or_ge (g.toVal : R) (((n : ℤ) + 1 : R) * (2 : R) ^ e_base) with hg_lt_hi | hg_ge_hi
          · exact hno_rep g hgs hgm ⟨hg_gt_lo, hg_lt_hi⟩
          · have hmono : roundUp v ≤ roundUp (g.toVal : R) :=
              roundUp_mono (le_trans (le_of_lt hv_hi) hg_ge_hi)
            rw [hru_v, hru_case, roundUp_idempotent (R := R) g (Or.inl hgs)] at hmono
            exact absurd hg_lt_succ (not_lt.mpr (FiniteFp.le_toVal_le R
              ((Fp.finite_le_finite_iff succ_fp g).mp hmono)))
      exact midpoint_outside_odd_interval hn_odd hn_large pred_fp succ_fp
        hpred_s hpred_m hsucc_s hsucc_m hpred_bound hsucc_bound hadj
    · -- Degenerate case: pred_fp.m = 0 → pred_fp.toVal = 0
      push_neg at hpred_m; have hm0 : pred_fp.m = 0 := by omega
      have hpred_val : (pred_fp.toVal : R) = 0 := by unfold FiniteFp.toVal; rw [hm0]; simp
      have hmid := midpoint_zero_pred_outside_odd_interval (R := R)
        (e_base := e_base) hn_odd hn_large hsucc_s
      rcases hmid with h | h
      · left; rw [hpred_val]; linarith
      · right; rw [hpred_val]; linarith
  · -- Case 2: roundUp v = Fp.infinite b (overflow)
    cases b with
    | true => exact absurd hru_case (findSuccessorPos_ne_neg_inf v hv_pos)
    | false =>
      have hru_v_inf : roundUp v = Fp.infinite false := hru_v.trans hru_case
      have hru_w_inf : roundUp w = Fp.infinite false := hru_eq.symm.trans hru_case
      set OT := FloatFormat.overflowThreshold R
      have hv_lt_OT : v < OT := by
        by_contra h; push_neg at h
        have := h_ge_inf v h
        rw [hv_rd, hrd_v] at this; exact absurd this (by simp)
      have hw_ge_OT : OT ≤ w := by
        by_contra h; push_neg at h
        have hrd_w : roundDown w = Fp.finite (findPredecessorPos w hw_pos) := by
          unfold roundDown; exact findPredecessor_pos_eq w hw_pos
        have := h_pos_succ_overflow w (findPredecessorPos w hw_pos) hw_pos h hrd_w hru_w_inf
        rw [hw_ru, hru_w_inf] at this; exact absurd this (by simp)
      have hOT_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < OT := lt_of_lt_of_le hv_lo hv_lt_OT.le
      have hOT_hi : OT < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base := lt_of_le_of_lt hw_ge_OT hw_hi
      exact overflow_threshold_outside_odd_interval hn_odd hn_large hOT_lo hOT_hi
  · exact absurd hru_case (findSuccessorPos_ne_nan v hv_pos)

/-- Crossing from roundDown to roundUp is impossible for roundNearestTiesToEven
    in an odd interval. -/
private theorem rnTE_no_crossing {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {v w : R} {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hv_pos : 0 < v) (hw_pos : 0 < w)
    (hv_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v)
    (hv_hi : v < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hw_hi : w < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hno_rep : noRepresentableIn (((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
        (((n : ℤ) + 1 : R) * (2 : R) ^ e_base))
    (hrd_eq : roundDown v = roundDown w)
    (hru_eq : roundUp v = roundUp w)
    (hrd_ne : roundDown v ≠ roundUp v)
    (hv_rd : roundNearestTiesToEven v = roundDown v)
    (hw_ru : roundNearestTiesToEven w = roundUp w) : False :=
  roundNearest_no_crossing hn_odd hn_large hv_pos hw_pos hv_lo hv_hi hw_hi
    hno_rep hrd_eq hru_eq hrd_ne hv_rd hw_ru
    rnEven_above_mid_roundUp rnEven_below_mid_roundDown
    rnEven_ge_inf rnEven_pos_succ_overflow

/-- Crossing from roundDown to roundUp is impossible for roundNearestTiesAwayFromZero
    in an odd interval. -/
private theorem rnTA_no_crossing {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {v w : R} {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1) (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    (hv_pos : 0 < v) (hw_pos : 0 < w)
    (hv_lo : ((n : ℤ) - 1 : R) * (2 : R) ^ e_base < v)
    (hv_hi : v < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hw_hi : w < ((n : ℤ) + 1 : R) * (2 : R) ^ e_base)
    (hno_rep : noRepresentableIn (((n : ℤ) - 1 : R) * (2 : R) ^ e_base)
        (((n : ℤ) + 1 : R) * (2 : R) ^ e_base))
    (hrd_eq : roundDown v = roundDown w)
    (hru_eq : roundUp v = roundUp w)
    (hrd_ne : roundDown v ≠ roundUp v)
    (hv_rd : roundNearestTiesAwayFromZero v = roundDown v)
    (hw_ru : roundNearestTiesAwayFromZero w = roundUp w) : False :=
  roundNearest_no_crossing hn_odd hn_large hv_pos hw_pos hv_lo hv_hi hw_hi
    hno_rep hrd_eq hru_eq hrd_ne hv_rd hw_ru
    (fun x m p s h1 h2 h3 h4 h5 h6 => rnAway_ge_mid_roundUp x m p s h1 h2 h3 h4 h5 h6.le)
    rnAway_lt_mid_roundDown rnAway_ge_inf rnAway_pos_succ_overflow

private theorem odd_interval_pos_and_noRep {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n) :
    0 < oddIntervalLo (R := R) n e_base ∧
      noRepresentableIn (oddIntervalLo (R := R) n e_base) (oddIntervalHi (R := R) n e_base) := by
  have hlo_pos : 0 < oddIntervalLo (R := R) n e_base := by
    unfold oddIntervalLo
    have hE_pos : (0 : R) < (2 : R) ^ e_base := zpow_pos (by norm_num : (0 : R) < 2) _
    have hn_ge : (1 : ℤ) ≤ (n : ℤ) - 1 := by
      have : 0 < 2 ^ (FloatFormat.prec.toNat + 3) := Nat.pos_of_ne_zero (by positivity)
      omega
    exact mul_pos (by exact_mod_cast hn_ge) hE_pos
  have hn_prec : 2 ^ FloatFormat.prec.toNat < n := by
    calc
      2 ^ FloatFormat.prec.toNat
          ≤ 2 ^ (FloatFormat.prec.toNat + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      _ < n := hn_large
  have hno_rep :
      noRepresentableIn (oddIntervalLo (R := R) n e_base) (oddIntervalHi (R := R) n e_base) := by
    intro f hfs hfm
    unfold oddIntervalLo oddIntervalHi
    exact no_representable_in_odd_interval hn_odd hn_prec f hfs hfm
  exact ⟨hlo_pos, hno_rep⟩

/-- `roundDown` is constant on odd intervals with odd center and large index. -/
theorem roundDown_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    roundDown v₁ = roundDown v₂ := by
  rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
  rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
  rcases odd_interval_pos_and_noRep (R := R) hn_odd hn_large with ⟨hlo_pos, hno_rep⟩
  exact roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi

/-- `roundUp` is constant on odd intervals with odd center and large index. -/
theorem roundUp_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    roundUp v₁ = roundUp v₂ := by
  rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
  rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
  rcases odd_interval_pos_and_noRep (R := R) hn_odd hn_large with ⟨hlo_pos, hno_rep⟩
  exact roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi

/-- `roundTowardZero` is constant on odd intervals with odd center and large index. -/
theorem roundTowardZero_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    roundTowardZero v₁ = roundTowardZero v₂ := by
  rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
  rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
  rcases odd_interval_pos_and_noRep (R := R) hn_odd hn_large with ⟨hlo_pos, hno_rep⟩
  exact roundTowardZero_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi

/-- `roundNearestTiesToEven` is constant on odd intervals with odd center and large index. -/
theorem rnEven_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    roundNearestTiesToEven v₁ = roundNearestTiesToEven v₂ := by
  rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
  rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
  rcases odd_interval_pos_and_noRep (R := R) hn_odd hn_large with ⟨hlo_pos, hno_rep⟩
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  have hrd : roundDown v₁ = roundDown v₂ :=
    roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  have hru : roundUp v₁ = roundUp v₂ :=
    roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  rcases rnTE_eq_roundDown_or_roundUp' v₁ with h1 | h1
  · rcases rnTE_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · rw [h1, h2, hrd]
    · rcases le_total v₁ v₂ with hle | hle
      · rw [h1, h2]
        by_cases hrDU : roundDown v₁ = roundUp v₁
        · exact hrDU.trans hru
        · exfalso
          exact rnTE_no_crossing hn_odd hn_large hv₁_pos hv₂_pos hv₁_lo hv₁_hi hv₂_hi
            hno_rep hrd hru hrDU h1 h2
      · have hmono := roundNearestTE_mono hle
        rw [h2, h1] at hmono
        rw [hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₂) hmono
        rw [h1, h2]
        exact hrd.trans heq
  · rcases rnTE_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · rcases le_total v₁ v₂ with hle | hle
      · have hmono := roundNearestTE_mono hle
        rw [h1, h2] at hmono
        rw [← hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₁) hmono
        rw [h1, h2, ← heq, hrd]
      · rw [h1, h2]
        by_cases hrDU : roundDown v₂ = roundUp v₂
        · exact hru.trans hrDU.symm
        · exfalso
          exact rnTE_no_crossing hn_odd hn_large hv₂_pos hv₁_pos hv₂_lo hv₂_hi hv₁_hi
            hno_rep hrd.symm hru.symm hrDU h2 h1
    · rw [h1, h2, hru]

/-- `roundNearestTiesAwayFromZero` is constant on odd intervals with odd center and large index. -/
theorem rnAway_eq_on_odd_interval {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    {n : ℕ} {e_base : ℤ}
    (hn_odd : n % 2 = 1)
    (hn_large : 2 ^ (FloatFormat.prec.toNat + 3) < n)
    {v₁ v₂ : R}
    (hv₁_in : inOddInterval (R := R) n e_base v₁)
    (hv₂_in : inOddInterval (R := R) n e_base v₂) :
    roundNearestTiesAwayFromZero v₁ = roundNearestTiesAwayFromZero v₂ := by
  rcases hv₁_in with ⟨hv₁_lo, hv₁_hi⟩
  rcases hv₂_in with ⟨hv₂_lo, hv₂_hi⟩
  rcases odd_interval_pos_and_noRep (R := R) hn_odd hn_large with ⟨hlo_pos, hno_rep⟩
  have hv₁_pos : 0 < v₁ := lt_trans hlo_pos hv₁_lo
  have hv₂_pos : 0 < v₂ := lt_trans hlo_pos hv₂_lo
  have hrd : roundDown v₁ = roundDown v₂ :=
    roundDown_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  have hru : roundUp v₁ = roundUp v₂ :=
    roundUp_eq_of_no_representable hlo_pos hno_rep hv₁_lo hv₁_hi hv₂_lo hv₂_hi
  rcases rnTA_eq_roundDown_or_roundUp' v₁ with h1 | h1
  · rcases rnTA_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · rw [h1, h2, hrd]
    · rcases le_total v₁ v₂ with hle | hle
      · rw [h1, h2]
        by_cases hrDU : roundDown v₁ = roundUp v₁
        · exact hrDU.trans hru
        · exfalso
          exact rnTA_no_crossing hn_odd hn_large hv₁_pos hv₂_pos hv₁_lo hv₁_hi hv₂_hi
            hno_rep hrd hru hrDU h1 h2
      · have hmono := roundNearestTA_mono hle
        rw [h2, h1] at hmono
        rw [hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₂) hmono
        rw [h1, h2]
        exact hrd.trans heq
  · rcases rnTA_eq_roundDown_or_roundUp' v₂ with h2 | h2
    · rcases le_total v₁ v₂ with hle | hle
      · have hmono := roundNearestTA_mono hle
        rw [h1, h2] at hmono
        rw [← hrd] at hmono
        have heq := Fp.le_antisymm (roundDown_le_roundUp v₁) hmono
        rw [h1, h2, ← heq, hrd]
      · rw [h1, h2]
        by_cases hrDU : roundDown v₂ = roundUp v₂
        · exact hru.trans hrDU.symm
        · exfalso
          exact rnTA_no_crossing hn_odd hn_large hv₂_pos hv₁_pos hv₂_lo hv₂_hi hv₁_hi
            hno_rep hrd.symm hru.symm hrDU h2 h1
    · rw [h1, h2, hru]

-- END EXTRACTED FROM Div.lean --

end OddInterval
