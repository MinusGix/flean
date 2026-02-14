import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Flean.Basic
import Flean.BitVecUtil
import Flean.RelativeError

namespace Fp

-- We need LinearOrderedField instead of LinearOrderedSemifield because we need to take absolute values.
-- (I mean, technically, if your R was purely positive then you don't need neg! So this limits the expressivity for our definition of ulp. But that's fine for now.)
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

/-- **Harrison's ULP** for a finite float, assuming unbounded exponent range.
For nonzero `f`, this equals `2^(⌊log₂|⌞f⌟|⌋ - prec + 1)`, computed from the float's
significand and exponent fields. Unlike `Fp.ulp`, this does NOT clamp the exponent to
`min_exp`, so for subnormal floats it can be smaller than the actual grid spacing. -/
def ulp_har [FloatFormat] (f : FiniteFp) : ℚ :=
  if f.m = 0 then 0
  else (2 : ℚ) ^ ((Nat.log 2 f.m : ℤ) + f.e - 2 * FloatFormat.prec + 2)

theorem ulp_har_zero [FloatFormat] : ulp_har (0 : FiniteFp) = 0 := by
  simp [ulp_har, FiniteFp.zero_def]

theorem ulp_har_pos [FloatFormat] (f : FiniteFp) (hm : 0 < f.m) : 0 < ulp_har f := by
  unfold ulp_har; simp [show f.m ≠ 0 from by omega]
  exact zpow_pos (by norm_num : (0 : ℚ) < 2) _

theorem ulp_har_ne_zero [FloatFormat] (f : FiniteFp) (hm : 0 < f.m) : ulp_har f ≠ 0 :=
  ne_of_gt (ulp_har_pos f hm)

theorem ulp_har_neg [FloatFormat] (f : FiniteFp) : ulp_har (-f) = ulp_har f := by
  simp [ulp_har]

/-- Normal significand implies positive significand. -/
private theorem isNormal_pos [FloatFormat] {m : ℕ} (hn : _root_.isNormal m) : 0 < m :=
  lt_of_lt_of_le (by positivity) hn.1

/-- Normal significand implies nonzero significand. -/
private theorem isNormal_ne_zero [FloatFormat] {m : ℕ} (hn : _root_.isNormal m) : m ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (isNormal_pos hn)

/-- For normal floats, `Nat.log 2 f.m = (prec - 1).toNat`. -/
private theorem nat_log_normal [FloatFormat] (f : FiniteFp) (hn : _root_.isNormal f.m) :
    Nat.log 2 f.m = (FloatFormat.prec - 1).toNat := by
  have hm_ne : f.m ≠ 0 := isNormal_ne_zero hn
  apply le_antisymm
  · have hlt : Nat.log 2 f.m < FloatFormat.prec.toNat :=
      (Nat.log_lt_iff_lt_pow (by norm_num) hm_ne).mpr f.valid.2.2.1
    have := FloatFormat.valid_prec; omega
  · exact (Nat.le_log_iff_pow_le (by norm_num) hm_ne).mpr hn.1

/-- For normal floats, Harrison's ULP equals the quantum `2^(e - prec + 1)`. -/
theorem ulp_har_normal_eq [FloatFormat] (f : FiniteFp) (hn : _root_.isNormal f.m) :
    ulp_har f = (2 : ℚ) ^ (f.e - FloatFormat.prec + 1) := by
  unfold ulp_har; rw [if_neg (isNormal_ne_zero hn)]
  congr 1; rw [nat_log_normal f hn, FloatFormat.prec_sub_one_toNat_eq]; ring

def ulp [FloatFormat] (v : R) : R :=
  -- Get the e for the power of two interval containing v |v| ∈ [2^e, 2^(e+1))
  let e : ℤ := Int.log 2 (|v|)
  let e := max e FloatFormat.min_exp
  2 ^ (e - FloatFormat.prec + 1)

theorem ulp_ne_zero [FloatFormat] (v : R)  : ulp v ≠ 0 := by
  apply zpow_ne_zero
  norm_num

theorem ulp_pos [FloatFormat] (v : R) : ulp v > 0 := by
  apply zpow_pos
  norm_num

/-- Distance between 1 and its floating-point successor. Sometimes called the 'machine epsilon'. This is the value of MATLAB's `eps`. -/
theorem ulp_one [FloatFormat] : ulp (1 : R) = ε := by
  delta ulp
  norm_num
  ring

def machineEpsilon [FloatFormat] : R := ulp (1 : R)

theorem ulp_zero [FloatFormat] : ulp (0 : R) = 2 ^ (-(FloatFormat.prec : ℤ) + 1) := by simp [ulp]

/-- Symmetric about 0. Which makes sense because floating point formats are symmetric about 0. -/
theorem ulp_eq_neg [FloatFormat] (v : R) : ulp (-v) = ulp v := by simp [ulp]

theorem ulp_ge [FloatFormat] : ∀ (v : R), 2^(FloatFormat.min_exp - FloatFormat.prec + 1) ≤ ulp v := by
  intro v
  delta ulp
  norm_num

/-- Being in the same power of two interval means the ULP is the same. -/
theorem ulp_step_log [FloatFormat] (v x : R) : Int.log 2 (|v|) = Int.log 2 (|x|) → ulp v = ulp x := by
  delta ulp
  intro h
  rw [h]

-- TODO: Can we clean this up, making it more clear about which parts are disjoint?
theorem ulp_step_log' [FloatFormat] (v x : R) : ulp v = ulp x →
  Int.log 2 (|v|) = Int.log 2 (|x|) ∨
  Int.log 2 (|v|) = FloatFormat.min_exp ∨
  Int.log 2 (|x|) = FloatFormat.min_exp ∨
  (Int.log 2 (|v|) < FloatFormat.min_exp ∧ Int.log 2 (|x|) < FloatFormat.min_exp) := by

  delta ulp
  norm_num
  intro hv
  cases' max_cases (Int.log 2 (|v|)) FloatFormat.min_exp with h h
  <;> cases' max_cases (Int.log 2 (|x|)) FloatFormat.min_exp with h' h'
  <;> rw [h.left, h'.left] at hv
  <;> rw [hv]
  <;> simp [hv, h, h']


-- theorem ulp_pow_mul [FloatFormat] (v : ℝ) (k : ℤ) : ulp (2^k * v) = 2^k * ulp v := by
--   delta ulp
--   norm_num
--   cases' abs_cases (2 ^ k * v) with h1 h2
--   · rw [h1.left]
--     have vnonneg : 0 ≤ v := by
--       have : 0 < (2 : ℝ) ^ k := by
--         apply zpow_pos_of_pos
--         norm_num
--       exact (mul_nonneg_iff_of_pos_left this).mp h1.right
--     rw [abs_of_nonneg vnonneg]
--     rw [← @Real.floor_logb_natCast 2 (2 ^ k * v), ← @Real.floor_logb_natCast 2 v]
--     norm_num
--     rw [Real.logb_mul]
--     cases' max_cases ⌊Real.logb 2 (2 ^ k) + Real.logb 2 v⌋ FloatFormat.min_exp with h3 h4
--     · rw [h3.left]
--       cases' max_cases ⌊Real.logb 2 v⌋ FloatFormat.min_exp with h5 h6
--       · rw [h5.left]



-- TODO: There's multiple definitions of ULP, prove equivalence conditions if they're useful.

-- theorem diff_lt_half_ulp_imp_rn [FloatFormat] (f : FiniteFp) (x : ℝ) : |f.toRat - x| < 1/2 * ulp x → Fp.finite f = round_nearest x := by
--   sorry

-- theorem Nat.pow_le_of_le_log_abs {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ Nat.log b y) : b ^ x ≤ |y| := by
--   refine (le_or_lt b 1).elim (fun hb => ?_) fun hb => (Nat.pow_le_iff_le_log hb hy).2 h
--   rw [Nat.log_of_left_le_one hb, Nat.le_zero] at h
--   rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

-- theorem Nat.pow_log_le_self_abs (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ Nat.log b x ≤ |x| :=
--   Nat.pow_le_of_le_log_abs hx le_rfl

-- TODO: should this be in mathlib?
theorem Int.zpow_log_le_abs_self {b : ℕ} {r : R} (hb : 1 < b) (rnz : r ≠ 0) (hra : |r| ≥ 1): (b : R) ^ Int.log b r ≤ |r| := by
  rcases le_total 1 r with hr1 | hr1
  · rw [Int.log_of_one_le_right _ hr1]
    rw [zpow_natCast, ← Nat.cast_pow, ← Nat.le_floor_iff (abs_nonneg _)]
    have h : b ^ Nat.log b ⌊r⌋₊ ≤ ⌊r⌋₊ := Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
    -- have h' : ⌊|r|⌋₊ ≤ |r| := Nat.floor_le (abs_nonneg r)
    have h'' : ⌊r⌋₊ ≤ ⌊|r|⌋₊ := by
      cases' abs_cases r with h1 h1
      · rw [h1.left]
      · linarith
    apply le_trans h h''
  · rw [Int.log_of_right_le_one _ hr1, zpow_neg, zpow_natCast, ← Nat.cast_pow]
    -- original version was for without abs
    -- exact inv_le_of_inv_le₀ (abs_pos.mpr rnz) (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)
    apply inv_le_of_inv_le₀ (abs_pos.mpr rnz)
    have h : ⌈|r|⁻¹⌉₊ ≤ b ^ Nat.clog b ⌈|r|⁻¹⌉₊ := by
      apply Nat.le_pow_clog hb
    simp_all only [ne_eq, Nat.ceil_le, Nat.cast_pow, ge_iff_le]
    cases' abs_cases r with h1 h1
    · rw [h1.left] at h ⊢
      exact h
    · rw [h1.left] at h ⊢
      rw [(@Nat.ceil_eq_zero R _ _ _ r⁻¹).mpr, Nat.clog_zero_right, pow_zero]
      rw [h1.left] at hra
      rw [show (1 : R) = (1 : R)⁻¹ by ring]
      apply (inv_le_inv₀ _ _).mpr hra
      linarith
      norm_num
      simp_all only [abs_eq_neg_self, inv_nonpos]

/-- In the normal range (|x| ≥ 2^min_exp), the ulp simplifies because the max with min_exp is trivial. -/
theorem ulp_normal_eq [FloatFormat] (x : R) (hx : 2^FloatFormat.min_exp ≤ |x|) :
    ulp x = 2^(Int.log 2 |x| - FloatFormat.prec + 1) := by
  unfold ulp
  have xnz : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith [two_zpow_pos' (R := R) FloatFormat.min_exp]
  have hge : FloatFormat.min_exp ≤ Int.log 2 |x| := by
    apply (Int.zpow_le_iff_le_log _ _).mp
    · exact_mod_cast hx
    · norm_num
    · exact abs_pos.mpr xnz
  simp [max_eq_left hge]

/-- For |x| ≥ 2^min_exp, the ratio ulp(x)/|x| ≤ 2^(1-prec) (machine epsilon).
This is the key bridge between ULP-based and relative error bounds. -/
theorem ulp_div_abs_le [FloatFormat] (x : R) (hx : 2^FloatFormat.min_exp ≤ |x|) :
    ulp x / |x| ≤ ε := by
  have xnz : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith [two_zpow_pos' (R := R) FloatFormat.min_exp]
  have xabspos : 0 < |x| := abs_pos.mpr xnz
  rw [ulp_normal_eq x hx, div_le_iff₀ xabspos]
  -- Goal: 2^(log 2 |x| - prec + 1) ≤ 2^(1-prec) * |x|
  -- Rewrite LHS: 2^(log - prec + 1) = 2^(log) * 2^(1-prec)
  rw [show Int.log 2 |x| - FloatFormat.prec + 1 = Int.log 2 |x| + (1 - FloatFormat.prec) from by ring]
  rw [← two_zpow_mul, mul_comm]
  apply mul_le_mul_of_nonneg_left (Int.zpow_log_le_self (by norm_num) xabspos)
  positivity

/-- Like `relativeError_ulp_upper_bound` but with ≤ instead of = for the absolute error.
For |x - y| ≤ α * ulp(x), the relative error is at most α * 2^(1-prec). -/
theorem relativeError_ulp_upper_bound_le [FloatFormat] (x : R) (y : FiniteFp) (α : R)
    (hα : 0 ≤ α) (xge : 2^FloatFormat.min_exp ≤ |x|) (hdiff : |x - ⌞y⌟| ≤ α * ulp x) :
    relativeError x y ≤ α * ε := by
  have xnz : x ≠ 0 := by
    intro h; rw [h, abs_zero] at xge; linarith [two_zpow_pos' (R := R) FloatFormat.min_exp]
  have xabspos : 0 < |x| := abs_pos.mpr xnz
  unfold relativeError
  rw [abs_div]
  apply div_le_of_le_mul₀ (le_of_lt xabspos) (by positivity)
  calc |x - ⌞y⌟| ≤ α * ulp x := hdiff
    _ = α * (ulp x / |x| * |x|) := by rw [div_mul_cancel₀ _ (ne_of_gt xabspos)]
    _ ≤ α * (ε * |x|) := by
        apply mul_le_mul_of_nonneg_left _ hα
        apply mul_le_mul_of_nonneg_right (ulp_div_abs_le x xge)
        exact le_of_lt xabspos
    _ = α * ε * |x| := by ring

/-- Given a floating point number `y` and a real number `x` in the normal range (≥ 2^min_exp),
there is a bound on the relative error between them in terms of (multiples of) ULP.
Specifically, if the absolute error is `α * ulp x`, then the relative error is at most
`α * 2^(1-prec)`. -/
theorem relativeError_ulp_upper_bound [FloatFormat] (x : R) (y : FiniteFp) (α : R) (xge : 2^FloatFormat.min_exp ≤ |x|) (hdiff : |x - ⌞y⌟| = α * ulp x) : relativeError x y ≤ α * ε := by
  have hpow : relativeError x y ≤ α * 2 ^ (1 - (FloatFormat.prec : ℤ)) := by
    delta relativeError
    delta ulp at hdiff
    norm_num at hdiff
    have xabspos : 0 < |x| := lt_of_le_of_lt' xge (two_zpow_pos' _)
    have xnz : x ≠ 0 := by simp_all only [abs_pos, ne_eq, not_false_eq_true]
    have xge' : FloatFormat.min_exp ≤ Int.log 2 |x| := by
      apply (Int.zpow_le_iff_le_log _ _).mp
      norm_cast
      norm_num
      apply abs_pos.mpr xnz

    rw [abs_div, hdiff]

    if hαz : α = 0 then
      -- Trivial case
      rw [hαz, zero_mul, zero_mul, zero_div]
    else
    have hα : 0 < α := by
      apply lt_of_le_of_ne
      apply le_of_mul_le_mul_right
      rw [zero_mul]
      rw [← hdiff]
      apply abs_nonneg
      exact two_zpow_pos' _
      exact (Ne.symm hαz)

    rw [← mul_div, max_eq_left xge']

    cases' abs_cases x with hx hx

    -- Get rid of abs
    rw [abs_of_nonneg hx.right]
    pick_goal 2; rw [abs_of_neg (by linarith)];

    -- Better form for the neg
    rw [show (2 ^ (Int.log 2 (-x) - ↑FloatFormat.prec + 1) / -x) = -(2 ^ (Int.log 2 (-x) - ↑FloatFormat.prec + 1) / x) by ring]

    -- Now we have the two simple branches where one is positive and the other is negative.
    all_goals apply (mul_le_mul_iff_of_pos_left hα).mpr -- get rid of the α
    all_goals rw [sub_add, zpow_sub₀ (by norm_num : (2 : R) ≠ 0)]

    all_goals rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ← mul_assoc, mul_comm x⁻¹, ← div_eq_mul_inv _ x, ← inv_zpow, inv_zpow', neg_sub]

    all_goals rw [← one_mul ((2 : R) ^ (1 - (FloatFormat.prec : ℤ)))]

    rw [← neg_mul]

    all_goals apply mul_le_mul

    pick_goal 2; rw [one_mul]
    pick_goal 2; rw [one_mul]; apply zpow_nonneg; norm_num
    pick_goal 2; norm_num

    pick_goal 3; rw [one_mul];
    pick_goal 3; rw [one_mul]; apply zpow_nonneg; norm_num
    pick_goal 3; norm_num

    rw [neg_div']

    rw [show -2 ^ Int.log 2 (-x) / x = 2 ^ Int.log 2 (-x) / -x by ring]

    all_goals apply (div_le_one (by linarith)).mpr
    all_goals apply Int.zpow_log_le_self (by norm_num) (by linarith)
  simpa [FloatFormat.eps] using hpow

/-- Given a floating point number `y` and a real number `x` in the normal range (≥ 2^min_exp),
there is a bound on the absolute error between them in terms of relative error and ULP.
Specifically, the absolute error is at most `relativeError * 2^prec * ulp x`.
This is the companion theorem to `relativeError_ulp_upper_bound`, showing the reverse relationship
between relative error and ULP. -/
theorem abs_error_relativeError_ulp_upper_bound [FloatFormat] (x : R) (y : FiniteFp) (xge : 2^FloatFormat.min_exp ≤ |x|) : |x - ⌞y⌟| ≤ (relativeError x y) * 2^(FloatFormat.prec : ℤ) * ulp x := by
  delta relativeError ulp
  -- norm_num
  -- TODO: Do we have to assume that x is in normal range?
  have xabspos : 0 < |x| := lt_of_le_of_lt' xge (two_zpow_pos' _)
  have xnz : x ≠ 0 := by simp_all only [abs_pos, ne_eq, not_false_eq_true]
  have xge' : FloatFormat.min_exp ≤ Int.log 2 |x| := by
    apply (Int.zpow_le_iff_le_log _ _).mp
    norm_cast
    norm_num
    apply abs_pos.mpr xnz
  rw [abs_div]
  rw [show |x - ⌞y⌟| / |x| = |x - ⌞y⌟| * |x|⁻¹ by ring]
  rw [show |x - ⌞y⌟| * |x|⁻¹ * 2 ^ (FloatFormat.prec : ℤ) * 2 ^ (Int.log 2 |x| ⊔ FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1) = |x - ⌞y⌟| * (|x|⁻¹ * (2 ^ (FloatFormat.prec : ℤ) * 2 ^ (Int.log 2 |x| ⊔ FloatFormat.min_exp - (FloatFormat.prec : ℤ) + 1))) by ring]

  by_cases h : |x - ⌞y⌟| = 0
  · rw [h, zero_mul]
  · apply (le_mul_iff_one_le_right (by positivity)).mpr
    apply (one_le_inv_mul₀ (by positivity)).mpr
    rw [two_zpow_mul]
    ring_nf
    rw [max_eq_left xge', add_comm]
    apply le_of_lt
    apply Int.lt_zpow_succ_log_self (by norm_num)

/-! ## Linking Harrison's ULP to the standard ULP -/

/-- The log of a positive float's value decomposes as `Nat.log 2 f.m + f.e - prec + 1`. -/
private theorem int_log_toVal_decompose [FloatFormat] (f : FiniteFp) (hs : f.s = false)
    (hm : 0 < f.m) :
    Int.log 2 |⌞f⌟[R]| = ↑(Nat.log 2 f.m) + f.e - FloatFormat.prec + 1 := by
  have hfpos := FiniteFp.toVal_pos f hs hm (R := R)
  rw [abs_of_pos hfpos, FiniteFp.toVal_pos_eq f hs]
  have hval_pos : (0 : R) < (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) :=
    mul_pos (by exact_mod_cast hm) (two_zpow_pos' _)
  apply le_antisymm
  · -- Upper: f.m < 2^(Nat.log+1), so f.m * 2^e < 2^(Nat.log+1+e), hence log < Nat.log+1+e
    have h_lt : (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) <
        (2 : R) ^ (↑(Nat.log 2 f.m) + 1 + (f.e - FloatFormat.prec + 1)) := by
      conv_rhs =>
        rw [show (↑(Nat.log 2 f.m : ℕ) : ℤ) + 1 + (f.e - FloatFormat.prec + 1) =
            ↑(Nat.log 2 f.m + 1 : ℕ) + (f.e - FloatFormat.prec + 1) from by push_cast; ring,
            ← two_zpow_mul]
      apply mul_lt_mul_of_pos_right _ (two_zpow_pos' _)
      rw [zpow_natCast]
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) f.m)
    have : Int.log 2 ((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) <
        ↑(Nat.log 2 f.m) + 1 + (f.e - FloatFormat.prec + 1) := by
      apply (Int.lt_zpow_iff_log_lt (show 1 < (2:ℕ) from by norm_num) hval_pos).mp
      exact_mod_cast h_lt
    omega
  · -- Lower: 2^(Nat.log) ≤ f.m, so 2^(Nat.log+e) ≤ f.m * 2^e, hence Nat.log+e ≤ log
    have h_le : (2 : R) ^ (↑(Nat.log 2 f.m) + (f.e - FloatFormat.prec + 1)) ≤
        (f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1) := by
      rw [← two_zpow_mul]
      exact mul_le_mul_of_nonneg_right
        (by rw [zpow_natCast]; exact_mod_cast Nat.pow_log_le_self 2 (by omega))
        (le_of_lt (two_zpow_pos' _))
    have : ↑(Nat.log 2 f.m) + (f.e - FloatFormat.prec + 1) ≤
        Int.log 2 ((f.m : R) * (2 : R) ^ (f.e - FloatFormat.prec + 1)) := by
      apply (Int.zpow_le_iff_le_log (show 1 < (2:ℕ) from by norm_num) hval_pos).mp
      exact_mod_cast h_le
    omega

/-- The log of a float's absolute value decomposes as `Nat.log 2 f.m + f.e - prec + 1`,
regardless of sign. -/
theorem int_log_toVal_decompose' [FloatFormat] (f : FiniteFp) (hm : 0 < f.m) :
    Int.log 2 |⌞f⌟[R]| = ↑(Nat.log 2 f.m) + f.e - FloatFormat.prec + 1 := by
  by_cases hs : f.s = false
  · exact int_log_toVal_decompose f hs hm
  · have hfs_true : f.s = true := by revert hs; cases f.s <;> simp
    rw [show |⌞f⌟| = |⌞(-f)⌟| from by
      rw [FiniteFp.toVal_neg_eq_neg, abs_neg],
      int_log_toVal_decompose (-f) (by simp [hfs_true]) (by simp; exact hm)]
    simp

/-- For normal floats, Harrison's ULP equals the standard ULP. -/
theorem ulp_har_eq_ulp [FloatFormat] (f : FiniteFp) (hn : _root_.isNormal f.m) :
    (ulp_har f : R) = ulp ⌞f⌟ := by
  rw [ulp_har_normal_eq f hn]; push_cast; unfold ulp; congr 1
  rw [int_log_toVal_decompose' (R := R) f (isNormal_pos hn), nat_log_normal f hn,
      FloatFormat.prec_sub_one_toNat_eq]
  have : FloatFormat.min_exp ≤ f.e := f.valid.1
  omega

/-- Harrison's ULP is at most the standard ULP (they differ only for subnormals). -/
theorem ulp_har_le_ulp [FloatFormat] (f : FiniteFp) (hm : 0 < f.m) :
    (ulp_har f : R) ≤ ulp ⌞f⌟ := by
  unfold ulp_har ulp; rw [if_neg (by omega : ¬f.m = 0)]; push_cast
  apply two_zpow_mono
  rw [int_log_toVal_decompose' (R := R) f hm]; omega

end Fp

-- #eval @Fp.ulp ℚ _ _ FloatFormat.Binary32.toFloatFormat 0
