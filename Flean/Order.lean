import Flean.Defs
import Flean.ToVal

namespace FiniteFp

variable [FloatFormat]

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
  -- have ha : (j k : FiniteFp) → (j.is_mag_le k) ↔ (j.m : R) * (2 : R) ^ (j.e - ↑FloatFormat.prec + 1) ≤ (k.m : R) * (2 : R) ^ (k.e - ↑FloatFormat.prec + 1) := by
  -- intro j k
  constructor
  · intro h
    unfold is_mag_le at h
    split_ifs at h with h1 h2
    · rw [h1]
      apply mul_le_mul_of_nonneg_right
      exact_mod_cast h
      linearize
    · --apply mul_le_of_le_div₀
      rw [mul_comm]
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
      apply (mul_le_mul_right ?_).mp
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
      apply (mul_lt_mul_right ?_).mp
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
    have y_m_too_large : 2^(FloatFormat.prec) ≤ y.m := by
      calc 2^FloatFormat.prec
        _ = 2^(FloatFormat.prec - 1 + 1) := by rw[Nat.sub_add_cancel (by fomega)]
        _ = 2^(FloatFormat.prec - 1) * 2 := by rw [Nat.pow_add_one]
        _ ≤ x.m * 2 := by omega
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
      rw [mul_le_mul_right] at hv
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
      have xm_too_large : 2^FloatFormat.prec ≤ x.m := by
        calc 2^FloatFormat.prec
          _ = 2^(FloatFormat.prec - 1 + 1) := by rw[Nat.sub_add_cancel (by fomega)]
          _ = 2^(FloatFormat.prec - 1) * 2 := by rw [Nat.pow_add_one]
          _ ≤ y.m * 2 := by omega
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

end FiniteFp
