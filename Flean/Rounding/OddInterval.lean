import Flean.Rounding.Rounding

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

/-- The sum of two multiples of 16 cannot equal `2*n` when `n` is odd.
    Key: `16 ∣ (a+b)` implies `4 ∣ (a+b)`, but `n` odd means `2n ≡ 2 (mod 4)`. -/
theorem sum_ne_double_odd {a b n : ℕ} (hn_odd : n % 2 = 1)
    (h16a : 16 ∣ a) (h16b : 16 ∣ b) : a + b ≠ 2 * n := by omega

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
      zpow_le_zpow_right₀ (by norm_num : (1:R) ≤ 2) ha_bound
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

end OddInterval
