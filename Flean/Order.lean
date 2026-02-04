import Flean.Defs
import Flean.ToVal
import Flean.CommonConstants

/-!

An ordering for floating point numbers.

Note that the *default* ordering we provide for floating point numbers is distinct from what the specification and programming languages has.
However, only in minor ways.

# FiniteFp
`FiniteFp` is given a signed magnitude total order.
The main exception to normal floating point ordering is that `-0 < +0`, as this allows us to define a stricter ordering, and make easier translations between Rational results and Floating Point numbers.

TODO: Define a `stdLt` for `FiniteFp` that is the same as the default ordering, with an easy way to translate conditions based on it into `<` with some side condition.

# Fp

-/

namespace FiniteFp

variable [FloatFormat]

section MagOrder

@[reducible]
def is_mag_lt (x y : FiniteFp) : Prop :=
  if x.e = y.e then x.m < y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) < y.m
  else x.m < y.m * 2^((y.e - x.e).natAbs)

@[reducible]
def is_lt (x y : FiniteFp) : Prop :=
  (x.s ∧ !y.s) ∨
  (!x.s ∧ !y.s ∧ x.is_mag_lt y) ∨
  (x.s ∧ y.s ∧ y.is_mag_lt x)

instance : LT FiniteFp := ⟨is_lt⟩

@[reducible]
def is_mag_le (x y : FiniteFp) : Prop :=
  if x.e = y.e then x.m ≤ y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) ≤ y.m
  else x.m ≤ y.m * 2^((y.e - x.e).natAbs)

theorem is_mag_le_refl (x : FiniteFp) : is_mag_le x x := by
  simp [is_mag_le]

def is_mag_eq (x y : FiniteFp) : Prop :=
  x.e = y.e ∧ x.m = y.m

@[reducible]
def is_le (x y : FiniteFp) : Prop := x < y ∨ x = y

theorem is_mag_lt_imp_is_mag_le {x y : FiniteFp} : x.is_mag_lt y → x.is_mag_le y := by
  unfold is_mag_lt is_mag_le
  intro h
  split_ifs at h with h1 h2
  · simp [h1, le_of_lt h]
  · simp [h1, h2, le_of_lt h]
  · simp [h1, h2, le_of_lt h]

theorem not_is_mag_lt_refl {x : FiniteFp} : ¬x.is_mag_lt x := by
  norm_num [is_mag_lt]

instance : LE FiniteFp := ⟨is_le⟩

theorem le_def (x y : FiniteFp) : x ≤ y ↔ (x < y ∨ x = y) := by rfl

theorem lt_def (x y : FiniteFp) : x < y ↔ (x.s ∧ !y.s) ∨
  (!x.s ∧ !y.s ∧ x.is_mag_lt y) ∨
  (x.s ∧ y.s ∧ y.is_mag_lt x) := by rfl

theorem lt_imp_is_le {x y : FiniteFp} : x < y → x ≤ y := by
  rw [lt_def, le_def, lt_def, eq_def]
  intro h
  simp_all

theorem lt_imp_ne {x y : FiniteFp} : x < y → x ≠ y := by
  rw [lt_def]
  intro h
  norm_num
  rw [eq_def]
  intro hn
  simp_all [is_mag_lt]

theorem not_lt_refl {x : FiniteFp} : ¬x < x := by
  simp [lt_def, not_is_mag_lt_refl]

theorem mag_lt_disjoint {x y : FiniteFp} : x.is_mag_lt y → ¬y.is_mag_lt x := by
  unfold is_mag_lt
  intro h
  split_ifs at h
  · simp_all [le_of_lt h]
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem is_mag_eq_refl (x : FiniteFp) : is_mag_eq x x := by
  simp [is_mag_eq]

theorem is_mag_eq_symm {x y : FiniteFp} : is_mag_eq x y → is_mag_eq y x := by
  unfold is_mag_eq
  grind

theorem is_mag_eq_trans {x y z : FiniteFp} : is_mag_eq x y → is_mag_eq y z → is_mag_eq x z := by
  unfold is_mag_eq
  grind

theorem is_mag_eq_imp_is_mag_le {x y : FiniteFp} : is_mag_eq x y → is_mag_le x y := by
  unfold is_mag_eq is_mag_le
  intro h
  simp_all


theorem neg_zero_lt_zero : (-0 : FiniteFp) < 0 := by
  simp [lt_def, zero_def, neg_def, isZero]

theorem zero_le_zero : (0 : FiniteFp) ≤ 0 := by
  simp only [zero_def, le_def, or_true]

theorem neg_zero_le_zero : (-0 : FiniteFp) ≤ 0 := by
  simp only [zero_def, neg_def, Bool.not_false, le_def, lt_def, and_self, Bool.not_true,
    Bool.false_eq_true, true_and, false_and, and_false, or_self, or_false, mk.injEq,
    Bool.true_eq_false, and_true]

theorem not_zero_le_neg_zero : ¬(0 : FiniteFp) ≤ (-0 : FiniteFp) := by
  simp only [zero_def, neg_def, Bool.not_false, le_def, lt_def, Bool.false_eq_true, Bool.not_true,
    and_self, false_and, and_false, true_and, or_self, mk.injEq, and_true, not_false_eq_true]

theorem mag_le_significand_le {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {j k : FiniteFp} : (j.is_mag_le k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  constructor
  · intro h
    unfold is_mag_le at h
    split_ifs at h with h1 h2
    · rw [h1]
      apply mul_le_mul_of_nonneg_right
      exact_mod_cast h
      linearize
    · rw [mul_comm]
      apply mul_le_mul_of_mul_div_le
      rw [← zpow_sub₀]
      norm_num
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      omega
      norm_num
      linearize
    · norm_num at h2
      apply mul_le_of_le_div₀
      · apply mul_nonneg
        linarith
        linearize
      · linearize
      · rw [mul_div_assoc, ← zpow_sub₀]
        norm_num
        rw [← zpow_natAbs_nonneg_eq_zpow]
        exact_mod_cast h
        norm_num
        omega
        norm_num
  · intro h
    unfold is_mag_le
    -- TODO: A lot of the logic is similar between forward/backward directions.
    split_ifs with h1 h2
    · rw [h1] at h
      apply (Nat.cast_le (α := R)).mp
      apply (mul_le_mul_iff_left₀ ?_).mp
      exact h
      linearize
    · apply (Nat.cast_le (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) / (2 : R)^(k.e - ↑FloatFormat.prec + 1) ≤ ↑k.m := by
        apply div_le_of_le_mul₀
        linearize
        linarith
        trivial
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      norm_num at h'
      trivial
      norm_num
      norm_num
      linarith
    · norm_num at h2
      apply (Nat.cast_le (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) / (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
        apply (le_div_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      norm_num at h'
      trivial
      norm_num
      norm_num
      omega

theorem mag_lt_significand_lt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {j k : FiniteFp} : (j.is_mag_lt k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) < (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  constructor
  · intro h
    unfold is_mag_lt at h
    split_ifs at h with h1 h2
    · rw [h1]
      apply (mul_lt_mul_iff_of_pos_right ?_).mpr
      assumption_mod_cast
      linearize
    · --rw [← zpow_natAbs_nonneg_eq_zpow]
      apply (mul_inv_lt_iff₀ ?_).mp -- why is there mul_le_mul_of_mul_div_le but no lt version and we have to do this rigmarole?
      rw [← inv_zpow, inv_zpow', mul_assoc, ← zpow_add₀]
      ring_nf
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      linarith
      norm_num
      linearize
    · rw [mul_comm]
      apply (lt_inv_mul_iff₀ ?_).mp
      rw [mul_comm, mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀]
      ring_nf
      rw [← zpow_natAbs_nonneg_eq_zpow]
      exact_mod_cast h
      norm_num
      linarith
      norm_num
      linearize
  · intro h
    unfold is_mag_lt
    split_ifs with h1 h2
    · rw [h1] at h
      apply (Nat.cast_lt (α := R)).mp
      apply (mul_lt_mul_iff_left₀ ?_).mp
      exact h
      linearize
    · apply (Nat.cast_lt (α := R)).mp
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [zpow_natAbs_nonneg_eq_zpow]
      norm_num
      have h' : (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) / (2 : R)^(k.e - ↑FloatFormat.prec + 1) < ↑k.m := by
        rw [div_eq_mul_inv]
        apply (mul_inv_lt_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      ring_nf at h'
      trivial
      norm_num
      norm_num
      linarith
    · norm_num at h2
      have h' : (j.m : R) < (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) / (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
        apply (lt_div_iff₀ ?_).mpr
        trivial
        linearize
      rw [mul_div_assoc, ← zpow_sub₀] at h'
      ring_nf at h'
      rw [← zpow_natAbs_nonneg_eq_zpow] at h'
      exact_mod_cast h'
      norm_num
      linarith
      norm_num



theorem le_toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x ≤ y → x.toVal (R := R) ≤ y.toVal (R := R) := by
  have hj : (j : FiniteFp) → 0 ≤ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
    intro j
    apply mul_nonneg
    linarith
    linearize
  intro h
  rw [le_def, lt_def] at h
  unfold toVal sign'
  rw [FloatFormat.radix_val_eq_two]
  rcases h with ⟨h1, h2⟩ | h3
  · simp_all
    have hx := hj x
    have hy := hj y
    linarith
  · rename_i h4
    cases' h4 with h1 h1
    · simp_all
      apply le_of_lt
      apply mag_lt_significand_lt.mp h1.right.right
    · simp_all
      apply le_of_lt
      apply mag_lt_significand_lt.mp h1.right.right
  · simp_all

/-- The order on floats is the same as the order on their values
    This allows easier proofs for various properties. -/
theorem toVal_le (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x y : FiniteFp} : x.toVal (R := R) ≤ y.toVal (R := R) → (¬x.isZero ∨ ¬y.isZero) → x ≤ y := by
  have hj : (j : FiniteFp) → 0 ≤ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) := by
    intro j
    apply mul_nonneg
    linarith
    linearize
  intro hv hnz
  have ho : (x y : FiniteFp) → x.e > y.e → ↑x.m * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) ≤ ↑y.m * (2 : R) ^ (y.e - ↑FloatFormat.prec + 1) → x.m * 2 ^ (x.e - y.e).natAbs < y.m := by
    intro x y hxy hv
    -- TOOD: I think I could merge hv and y_m too large into one calc
    have hv : ↑x.m * (2 : R) ^ (x.e - y.e).natAbs ≤ ↑y.m := by
      rw [← mul_inv_le_iff₀ (by linearize), mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀ (by norm_num)] at hv
      ring_nf at hv
      rw [← zpow_natAbs_nonneg_eq_zpow (by linarith) (by linarith)] at hv
      exact hv
    apply lt_of_le_of_ne (by exact_mod_cast hv)
    intro heq
    have := valid_min_exp_lt_imp_isNormal (by linarith [y.valid_min_exp])
    unfold isNormal at this
    have yvf := y.valid.right.right.left
    have y_m_too_large : (2 : ℕ)^FloatFormat.prec.toNat ≤ y.m := by
      have hprec := FloatFormat.valid_prec
      have hprecm1 : (FloatFormat.prec - 1).toNat = FloatFormat.prec.toNat - 1 :=
        FloatFormat.prec_sub_one_toNat_eq_toNat_sub
      calc (2 : ℕ)^FloatFormat.prec.toNat
        _ = 2^(FloatFormat.prec.toNat - 1 + 1) := by
          congr 1
          have hp := FloatFormat.prec_toNat_pos
          omega
        _ = 2^(FloatFormat.prec.toNat - 1) * 2 := by rw [Nat.pow_add_one]
        _ ≤ x.m * 2 := by rw [← hprecm1]; omega
        _ ≤ x.m * 2^((x.e - y.e).natAbs) := by
          gcongr
          apply le_self_pow₀ (by norm_num) (by omega)
        _ = y.m := by omega
    omega -- contradiction

  have hol : (x y : FiniteFp) → x.m * (2 : R)^(x.e - ↑FloatFormat.prec + 1) ≤ y.m * (2 : R)^(y.e - ↑FloatFormat.prec + 1) → x.is_mag_lt y ∨ x.e = y.e ∧ x.m = y.m := by
    intro x y hv
    rw [is_mag_lt]
    split_ifs with he he1
    · rw [he] at hv
      rw [mul_le_mul_iff_left₀] at hv
      norm_num [he]
      apply lt_or_eq_of_le
      assumption_mod_cast
      linearize
    · left
      apply ho x y he1 hv
    · norm_num at he1
      have he1 := lt_of_le_of_ne he1 he
      left
      have hv : ↑x.m ≤ ↑y.m * (2 : R) ^ (y.e - x.e).natAbs := by
        rw [← le_mul_inv_iff₀ (by linearize), mul_assoc, ← inv_zpow, inv_zpow', ← zpow_add₀ (by norm_num)] at hv
        ring_nf at hv
        rw [← zpow_natAbs_nonneg_eq_zpow (by norm_num) (by linarith)] at hv
        exact hv
      apply lt_of_le_of_ne (by exact_mod_cast hv)

      intro heq
      have := x.valid.right.right.left
      have is_normal_y : _root_.isNormal y.m := valid_min_exp_lt_imp_isNormal (by linarith [x.valid_min_exp])
      have xm_too_large : (2 : ℕ)^FloatFormat.prec.toNat ≤ x.m := by
        have hprec := FloatFormat.valid_prec
        have hprecm1 : (FloatFormat.prec - 1).toNat = FloatFormat.prec.toNat - 1 :=
          FloatFormat.prec_sub_one_toNat_eq_toNat_sub
        calc (2 : ℕ)^FloatFormat.prec.toNat
          _ = 2^(FloatFormat.prec.toNat - 1 + 1) := by
            congr 1
            have hp := FloatFormat.prec_toNat_pos
            omega
          _ = 2^(FloatFormat.prec.toNat - 1) * 2 := by rw [Nat.pow_add_one]
          _ ≤ y.m * 2 := by rw [← hprecm1]; omega
          _ ≤ y.m * 2^((y.e - x.e).natAbs) := by
            gcongr
            apply le_self_pow₀ (by norm_num) (by omega)
          _ = x.m := by omega
      omega

  unfold isZero at hnz
  unfold toVal sign' at hv
  norm_num at hv
  rw [le_def, lt_def, eq_def]
  rw [FloatFormat.radix_val_eq_two] at hv
  split_ifs at hv with h1 h2 h3
  · norm_num [h1, h2] at hv ⊢
    rw [eq_comm (a := x.e), eq_comm (a := x.m)] -- why does apply consider Or/And order relevant?
    apply hol y x hv
  · norm_num [h1, h2] at hv ⊢
  · norm_num [h1, h3] at hv ⊢
    have hx := hj x
    have hy := hj y
    have hn : 0 = ↑x.m * (2 : R) ^ (x.e - ↑FloatFormat.prec + 1) := by linarith
    have hn : 0 = ↑y.m * (2 : R) ^ (y.e - ↑FloatFormat.prec + 1) := by linarith
    simp_all [zpow_ne_zero]
  · norm_num [h1, h3] at hv ⊢
    apply hol x y hv

/-- toVal_le but where you handle the case where the values are zero, proving it manually, since 0 and -0 are not necessarily distinguished in R -/
theorem toVal_le_handle (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {x y : FiniteFp} : x.toVal (R := R) ≤ y.toVal (R := R) → ((x.isZero ∧ y.isZero) → x ≤ y) → x ≤ y := by
  intro hxy
  intro hnz
  if hz : x.isZero ∧ y.isZero then
    apply hnz hz
  else
    apply toVal_le R hxy
    rw [not_and_or] at hz
    exact hz

/-- Two floats are ordered the same as their values, as long as they are non-zero -/
theorem lt_toVal_lt (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x < y → (¬x.isZero ∨ ¬y.isZero) → x.toVal (R := R) < y.toVal (R := R) := by
  intro h hnz
  apply lt_of_le_of_ne
  · apply le_toVal_le
    apply lt_imp_is_le h
  · apply imp_toVal_ne _ hnz
    apply lt_imp_ne h

/-- If the values are ordered, then the floats are ordered -/
theorem toVal_lt (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x y : FiniteFp} : x.toVal (R := R) < y.toVal (R := R) → x < y := by
  intro hlt
  rw [lt_def]
  unfold toVal sign' at hlt
  rw [FloatFormat.radix_val_eq_two] at hlt
  split_ifs at hlt with h1 h2 h3
  · norm_num [h1, h2]
    norm_num at hlt
    apply mag_lt_significand_lt.mpr hlt
  · norm_num [h1, h2]
  · norm_num [h1, h3]
    norm_num at hlt
    have hx := toVal_mag_nonneg' R x
    have hy := toVal_mag_nonneg' R y
    linarith
  · norm_num [h1, h3]
    norm_num at hlt
    apply mag_lt_significand_lt.mpr hlt

theorem is_le_trans {a b c : FiniteFp} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  have hab := le_toVal_le ℚ hab
  have hbc := le_toVal_le ℚ hbc
  apply toVal_le_handle ℚ (by linarith)
  intro hz
  rw [isZero_iff, isZero_iff] at hz
  rcases hz with ⟨h1 | h2, h3 | h4⟩
  · simp [le_def, h1, h3]
  · have := not_zero_le_neg_zero
    rename_i ha hb
    rw [h1] at ha
    rw [h4] at hb
    simp_all [le_def, lt_def, zero_def, neg_def, is_mag_lt, toVal, sign', FloatFormat.radix_val_eq_two]
    aesop
  · simp [neg_zero_le_zero, h2, h3]
  · simp [le_def, h2, h4]

theorem is_mag_lt_trans {a b c : FiniteFp} : a.is_mag_lt b → b.is_mag_lt c → a.is_mag_lt c := by
  intro hab hbc
  have hab := (mag_lt_significand_lt (R := ℚ)).mp hab
  have hbc := (mag_lt_significand_lt (R := ℚ)).mp hbc
  apply (mag_lt_significand_lt (R := ℚ)).mpr
  linarith

theorem is_lt_trans {a b c : FiniteFp} : a < b → b < c → a < c := by
  intro hab hbc
  rw [lt_def] at hab hbc ⊢
  cases' hab with h1 h1
  <;> cases' hbc with h2 h2
  · grind
  · grind
  · grind
  · cases' h1 with h1 h1
    <;> cases' h2 with h2 h2
    · have := is_mag_lt_trans h1.right.right h2.right.right
      grind
    · grind
    · grind
    · have := is_mag_lt_trans h2.right.right h1.right.right
      grind

theorem pos_nz_is_mag_lt_imp_nz {x y : FiniteFp} (hs : x.s = false) (hnz : ¬x.isZero): x.is_mag_lt y → ¬y.isZero := by
  intro hm
  unfold isZero at hnz ⊢
  unfold is_mag_lt at hm
  split_ifs at hm
  · grind
  · grind
  · simp_all only [gt_iff_lt, not_lt]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [zero_mul, not_lt_zero']

theorem mag_le_total (a b : FiniteFp) : a.is_mag_le b ∨ b.is_mag_le a := by
  rw [mag_le_significand_le (R := ℚ), mag_le_significand_le (R := ℚ)]
  apply le_total

-- theorem mag_le_iff_mag_lt_or_eq (a b : FiniteFp) : a.is_mag_le b ↔ a.is_mag_lt b ∨ (a.e = b.e ∧ a.m = b.m) := by
--   rw [mag_le_significand_le (R := ℚ), mag_lt_significand_lt (R := ℚ)]
--   constructor
--   · intro h

    -- if h1 : a.e = b.e ∧ a.m = b.m then
    --   grind
    -- else
    --   left
    --   apply lt_of_le_of_ne h
    --   rw [not_and_or] at h1
    --   cases' h1
    --   ·

theorem mag_le_imp_le_of_pos {x y : FiniteFp} : !x.s → !y.s → x.is_mag_le y → x ≤ y := by
  intro h1 h2 h3

  have h3 := (mag_le_significand_le (R := ℚ)).mp h3
  apply toVal_le_handle ℚ
  · unfold toVal sign'
    norm_num at h1 h2
    norm_num [h1, h2]
    trivial
  · intro nz
    rw [isZero_iff, isZero_iff] at nz
    rcases nz with ⟨h1 | h2, h3 | h4⟩
    · simp [le_def, h1, h3]
    · have := not_zero_le_neg_zero
      rename_i ha hb
      rw [h1] at ha
      rw [h4] at hb
      simp_all only [zero_def, Bool.not_false, neg_def, Bool.not_true, Bool.false_eq_true]
    · simp [neg_zero_le_zero, h2, h3]
    · simp [le_def, h2, h4]

-- theorem mag_lt_total {a b : FiniteFp} : a.is_mag_lt b ∨ b.is_mag_lt a ∨ a = b := by
--   rw [mag_lt_significand_lt (R := ℚ), mag_lt_significand_lt (R := ℚ)]
--   -- apply le_total
--   rw [show ↑a.m * 2 ^ (a.e - ↑FloatFormat.prec + 1) < ↑b.m * (2 : ℚ) ^ (b.e - ↑FloatFormat.prec + 1) ↔ ( ↑a.m * 2 ^ (a.e - ↑FloatFormat.prec + 1) < ↑b.m * (2 : ℚ) ^ (b.e - ↑FloatFormat.prec + 1) ∨ a = b) by ring_nf]
--   rw [← le_iff_lt_or_eq]
  -- have h : (x y : ℚ) → (x < y ∨ x = y) ↔ x ≤ y := by
  --   intro x y
  --   constructor
  --   · intro h
  --     rw []

theorem mag_le_imp_le_of_neg {x y : FiniteFp} : x.s → y.s → x.is_mag_le y → y ≤ x:= by
  intro h1 h2 h3
  have h3 := (mag_le_significand_le (R := ℚ)).mp h3
  apply toVal_le_handle ℚ
  · unfold toVal sign'
    simp [h1, h2]
    trivial
  · intro nz
    rw [isZero_iff, isZero_iff] at nz
    rcases nz with ⟨h1 | h2, h3 | h4⟩
    · simp [le_def, h1, h3]
    · have := not_zero_le_neg_zero
      rename_i hb ha
      rw [h1] at ha
      rw [h4] at hb
      simp_all only [zero_def, Bool.not_false, neg_def, Bool.not_true, Bool.false_eq_true]
    · simp [neg_zero_le_zero, h2, h3]
    · simp [le_def, h2, h4]

section Decidable

-- Decidable equality
def beq (x y : FiniteFp) : Bool :=
  x.s == y.s && x.e == y.e && x.m == y.m

-- Boolean version of is_mag_lt
def bmag_lt (x y : FiniteFp) : Bool :=
  if h : x.e = y.e then x.m < y.m
  else if x.e > y.e then x.m * 2^((x.e - y.e).natAbs) < y.m
  else x.m < y.m * 2^((y.e - x.e).natAbs)

-- Boolean version of is_lt
def blt (x y : FiniteFp) : Bool :=
  (x.s && !y.s) ||
  (!x.s && !y.s && x.bmag_lt y) ||
  (x.s && y.s && y.bmag_lt x)

-- Finally, boolean version of is_le
def ble (x y : FiniteFp) : Bool :=
  blt x y || beq x y

theorem beq_iff_eq {a b : FiniteFp} : (beq a b) = true ↔ a = b := by
  norm_num [beq, eq_def]
  grind

theorem blt_iff_lt {a b : FiniteFp} : (blt a b) = true ↔ a < b := by
  norm_num [blt, lt_def, bmag_lt, is_mag_lt]
  grind

theorem ble_iff_le {a b : FiniteFp} : (ble a b) = true ↔ a ≤ b := by
  norm_num [ble, le_def, lt_def, blt, beq, eq_def, is_mag_lt, bmag_lt]
  grind

instance (x y : FiniteFp) : Decidable (x < y) := decidable_of_iff (blt x y) blt_iff_lt

instance (x y : FiniteFp) : Decidable (x ≤ y) := decidable_of_iff (ble x y) ble_iff_le

instance : DecidableEq FiniteFp := fun a b => decidable_of_iff (beq a b) beq_iff_eq

end Decidable

instance : Preorder FiniteFp := {
  le_refl := by simp [le_def]
  le_trans := by apply is_le_trans
  lt := fun a b => a < b
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro ha
      split_ands
      · rw [le_def]
        left; exact ha
      · intro hba
        cases' hba with h1 h2
        · exact not_lt_refl (is_lt_trans ha h1)
        · rw [h2] at ha
          apply not_lt_refl ha
    · intro ha
      rw [le_def] at ha
      cases' ha.left with h1 h2
      · trivial
      · exfalso
        have : b ≤ a := by
          rw [h2]
          simp [le_def]
        apply ha.right this
}

instance : PartialOrder FiniteFp := {
  le_antisymm := by
    intro a b hab hba
    rw [le_def] at hab hba
    cases' hab with h1 h1
    · have h2 := lt_asymm h1
      grind
    · trivial
}

instance : LinearOrder FiniteFp := {
  le_total := by
    intro a b
    -- rw [le_def, le_def, lt_def, lt_def]
    if ha : a.s then
      if hb : b.s then
        have := mag_le_total a b
        cases' this with h1 h1
        · right
          apply mag_le_imp_le_of_neg ha hb h1
        · left
          apply mag_le_imp_le_of_neg hb ha h1
      else
        simp_all [le_def, lt_def]
    else
      if hb : b.s then
        simp_all [le_def, lt_def]
      else
        have := mag_le_total a b
        cases' this with h1 h1
        · left
          apply mag_le_imp_le_of_pos (by grind) (by grind) h1
        · right
          apply mag_le_imp_le_of_pos (by grind) (by grind) h1
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
}

theorem le_largestFiniteFloat {a : FiniteFp} : a ≤ FiniteFp.largestFiniteFloat := by
  apply toVal_le_handle ℚ
  apply finite_le_largestFiniteFloat
  intro h
  exfalso
  have h := h.right
  unfold largestFiniteFloat isZero at h
  norm_num at h
  have := FloatFormat.prec_pow_le (R := ℕ)
  omega

instance : Top FiniteFp := ⟨FiniteFp.largestFiniteFloat⟩
instance : Bot FiniteFp := ⟨-FiniteFp.largestFiniteFloat⟩

theorem top_def : ⊤ = FiniteFp.largestFiniteFloat := rfl
theorem bot_def : ⊥ = -FiniteFp.largestFiniteFloat := rfl

instance : OrderTop FiniteFp := {
  le_top := by
    rw [top_def]
    apply le_largestFiniteFloat
}

instance : OrderBot FiniteFp := {
  bot_le := by
    rw [bot_def]
    intro a
    apply toVal_le_handle ℚ
    rw [FiniteFp.toVal_neg_eq_neg, neg_le, ← FiniteFp.toVal_neg_eq_neg]
    apply finite_le_largestFiniteFloat
    intro h
    have h := h.left
    rw [isZero, neg_def, largestFiniteFloat] at h
    norm_num at h
    have := FloatFormat.prec_pow_le (R := ℕ)
    omega
}

instance : BoundedOrder FiniteFp := {}

instance : Lattice FiniteFp := inferInstance

end MagOrder

section StdOrder

-- TODO: should this be in the main file?

@[reducible]
def stdEquiv (x y : FiniteFp) : Prop :=
  (x.isZero ∧ y.isZero) ∨ -- -0 == 0
  x = y

@[reducible]
def stdLt (x y : FiniteFp) : Prop :=
  ((x.s ∧ !y.s) ∧ (¬x.isZero ∨ ¬y.isZero)) ∨
  (!x.s ∧ !y.s ∧ x.is_mag_lt y) ∨
  (x.s ∧ y.s ∧ y.is_mag_lt x)

@[reducible]
def stdLe (x y : FiniteFp) : Prop :=
  x.stdLt y ∨ x.stdEquiv y

section StdEquiv

@[simp]
theorem stdEquiv_refl {x : FiniteFp} : x.stdEquiv x := by grind

theorem stdEquiv_symm {x y : FiniteFp} : x.stdEquiv y → y.stdEquiv x := by grind

@[simp]
theorem stdEquiv_trans {x y z : FiniteFp} : x.stdEquiv y → y.stdEquiv z → x.stdEquiv z := by grind

@[simp]
theorem stdEquiv_zero_neg_zero : (0 : FiniteFp).stdEquiv (-0) := by
  simp [FiniteFp.zero_def, FiniteFp.neg_def, stdEquiv, isZero]

@[simp]
theorem stdEquiv_neg_zero_zero : (-0 : FiniteFp).stdEquiv 0 := by
  simp [FiniteFp.neg_def, FiniteFp.zero_def, stdEquiv, isZero]

def stdEquiv_equivalence : Equivalence stdEquiv := {
  refl := λ _ => stdEquiv_refl
  symm := stdEquiv_symm
  trans := stdEquiv_trans
}

end StdEquiv

section StdLt

@[simp]
theorem not_stdLt_refl {x : FiniteFp} : ¬x.stdLt x := by grind

@[simp]
theorem zero_not_stdLt_neg_zero : ¬(0 : FiniteFp).stdLt (-0) := by
  simp [stdLt, zero_def, neg_def]

@[simp]
theorem neg_zero_not_stdLt_zero : ¬(-0 : FiniteFp).stdLt 0 := by
  simp [stdLt, zero_def, neg_def, isZero]

theorem stdLt_imp_lt {x y : FiniteFp} (hlt : x.stdLt y) : x < y := by
  rw [lt_def]
  grind

theorem lt_imp_stdLt {x y : FiniteFp} (hlt : x < y) (hnz : ¬x.isZero ∨ ¬y.isZero): x.stdLt y := by
  rw [lt_def] at hlt
  grind

theorem lt_imp_stdLt_left_nz {x y : FiniteFp} (hlt : x < y) (hnz : ¬x.isZero) : x.stdLt y := lt_imp_stdLt hlt (Or.inl hnz)

theorem lt_imp_stdLt_right_nz {x y : FiniteFp} (hlt : x < y) (hnz : ¬y.isZero) : x.stdLt y := lt_imp_stdLt hlt (Or.inr hnz)

theorem stdLt_trans {x y z : FiniteFp} (hxy : x.stdLt y) (hyz : y.stdLt z) : x.stdLt z := by
  unfold stdLt at *
  have := @pos_nz_is_mag_lt_imp_nz
  cases' hxy with h1 h1
  <;> cases' hyz with h2 h2
  <;> simp_all
  · grind
  · cases' h2.right with h3 h3
    · left
      unfold is_mag_lt at h1
      split_ifs at h1 with h4 h5
      · grind
      · grind
      · have ha : 0 < 2 ^ (x.e - y.e).natAbs := by linearize
        have hb : 0 < x.m * 2 ^ (x.e - y.e).natAbs := by omega
        have hc : 0 < x.m := by
          apply Nat.pos_of_mul_pos_right hb
        omega
    · grind
  · cases' h1 with h1 h1
    <;> cases' h2 with h2 h2
    · simp_all
      apply is_mag_lt_trans h1.right h2.right.right
    · grind
    · grind
    · simp_all
      apply is_mag_lt_trans h2.right.right h1.right


-- TODO: toVal_stdLt proofs?

end StdLt

section StdLe

theorem stdLe_refl {x : FiniteFp} : x.stdLe x := by grind

theorem stdLe_stdEquiv {x y z : FiniteFp} (hnz : ¬y.isZero ∨ ¬z.isZero) (hxy : x.stdLe y) (hyz : y.stdEquiv z) : x.stdLe z := by
  if h2 : y.isZero then
    grind
  else
    grind

theorem stdLe_trans {x y z : FiniteFp} (hxy : x.stdLe y) (hyz : y.stdLe z) : x.stdLe z := by
  have h1 := @stdLt_trans
  have h2 := @stdEquiv_trans
  unfold stdLe at hxy hyz ⊢
  cases' hxy with h1 h1
  <;> cases' hyz with h2 h2
  · left
    apply stdLt_trans h1 h2
  · apply @stdLe_stdEquiv _ x y z
    · sorry
    · grind
    · grind
  · sorry
  · grind


end StdLe

section Decidable

def bstdLt (x y : FiniteFp) : Bool :=
  (x.s && !y.s && (¬x.isZero || ¬y.isZero)) ||
  (!x.s && !y.s && x.bmag_lt y) ||
  (x.s && y.s && y.bmag_lt x)

theorem bstdLt_iff_stdLt {x y : FiniteFp} : (bstdLt x y) = true ↔ x.stdLt y := by
  norm_num [bstdLt, stdLt, bmag_lt, is_mag_lt]
  grind

end Decidable

end StdOrder

end FiniteFp

namespace Fp

variable [FloatFormat]

@[reducible]
def is_total_lt (x y : Fp) : Prop :=
  match (x, y) with
  | (.finite x, .finite y) => x < y
  | (.infinite b, .infinite c) => b = false && c = true
  | (.infinite b, .finite _) => b
  | (.finite _, .infinite b) => !b
  | (.NaN, _) => true -- total order has NaN less than everything
  | (_, .NaN) => false

instance : LT Fp := ⟨is_total_lt⟩

@[reducible]
def is_total_le (x y : Fp) : Prop :=
  is_total_lt x y ∨ x = y

instance : LE Fp := ⟨is_total_le⟩

theorem lt_def (x y : Fp) : x < y ↔ (match (x, y) with
  | (.finite x, .finite y) => x < y
  | (.infinite b, .infinite c) => b = false && c = true
  | (.infinite b, .finite _) => b
  | (.finite _, .infinite b) => !b
  | (.NaN, _) => true
  | (_, .NaN) => false) := by rfl

theorem le_def (x y : Fp) : x ≤ y ↔ ((match (x, y) with
  | (.finite x, .finite y) => x < y
  | (.infinite b, .infinite c) => b = false && c = true
  | (.infinite b, .finite _) => b
  | (.finite _, .infinite b) => !b
  | (.NaN, _) => true
  | (_, .NaN) => false) ∨ x = y) := by rfl

-- theorem lt_cases {x y : Fp} :

protected theorem lt_imp_le {x y : Fp} : x < y → x ≤ y := by
  intro h
  rw [le_def]
  left
  exact h

-- theorem lt_imp_ne {x y : Fp} : x < y → x ≠ y := by
--   intro h
--   rw [lt_def] at h
--   simp_all

/-- Ordering on Fp.finite values corresponds to FiniteFp ordering -/
theorem finite_le_finite_iff (x y : FiniteFp) : Fp.finite x ≤ Fp.finite y ↔ x ≤ y := by
  rw [le_def, FiniteFp.le_def]
  simp only [Fp.finite.injEq]

theorem le_refl (x : Fp) : x ≤ x := by
  rw [le_def]; right; rfl

/-- Transitivity for Fp.finite values -/
theorem finite_le_trans {x y z : FiniteFp} (hxy : Fp.finite x ≤ Fp.finite y)
    (hyz : Fp.finite y ≤ Fp.finite z) : Fp.finite x ≤ Fp.finite z := by
  rw [finite_le_finite_iff] at hxy hyz ⊢
  exact FiniteFp.is_le_trans hxy hyz

end Fp
