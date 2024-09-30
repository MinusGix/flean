import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LiftLets

import Flean.Basic
import Flean.BitVecUtil
import Flean.Encoding.Basic

namespace Fp

def FpEquiv [FloatFormat] (x y : FloatBits) : Prop := x = y ∨ (x.isNaN ∧ y.isNaN)

instance [FloatFormat] : DecidableRel FpEquiv := by
  intro x y
  unfold FpEquiv
  infer_instance



-- TODO: proof that a = b ↔ a.toBits ≃ b.toBits
/-! A setoid which considers equivalence like how `Fp` does, treating NaNs as equivalent -/
def FpSetoid [FloatFormat] : Setoid FloatBits where
  /- If they're both NaN we consider them equivalent (in the higher level representation of Fp)-/
  r := FpEquiv
  iseqv := {
    refl := by
      intro x
      unfold FpEquiv FloatBits.isNaN
      left
      rfl
    symm := by
      unfold FpEquiv
      intro x y h
      cases h with
      | inl h_1 => subst h_1; left; rfl
      | inr h_2 => right; symm; exact h_2
    trans := by
      unfold FpEquiv
      intro x y z h1 h2
      cases h1 with
      | inl h =>
        cases h2 with
        | inl h_1 =>
          subst h h_1; left; rfl
        | inr h_2 => subst h; right; exact h_2
      | inr h_1 =>
        cases h2 with
        | inl h => subst h; right; exact h_1
        | inr h_2 =>
          right
          obtain ⟨⟨left1, right1⟩, _⟩ := h_1
          obtain ⟨_, right2⟩ := h_2

          unfold FloatBits.isTSignificandZero at right1
          apply And.intro
          · apply And.intro
            · assumption
            · simp_all only [ne_eq, BitVec.ofNat_eq_ofNat, not_false_eq_true]
          · assumption
  }

def FpQuotient [FloatFormat] : Type := Quotient FpSetoid

-- TODO: it may be possible to have a general way to turn a proof that applies to `Fp` and make it apply to `FpQuotient`..

@[reducible]
def FpQuotient.mk [FloatFormat] (f : FloatBits) : FpQuotient := Quotient.mk FpSetoid f

@[reducible]
def FpQuotient.isInfinite [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f FloatBits.isInfinite (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      unfold FloatBits.isInfinite
      unfold FloatBits.isNaN at h
      simp only [h, and_false]
  )

@[reducible]
def FpQuotient.isNaN [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f FloatBits.isNaN (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      simp only [h]
  )

def FpQuotient.isFinite [FloatFormat] (f : FpQuotient) : Prop :=
  Quotient.liftOn f FloatBits.isFinite (by
    intro a b h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      unfold FloatBits.isFinite
      simp only [h, not_true_eq_false, false_and]
  )

-- Normal `sign` can't be equivalent over the quotient because two NaN values can have different signs
-- We simply say that an FpQuotient sign is always positive for NaN values, but doing such in FloatBits would be confusing.
def FpQuotient.fake_sign [FloatFormat] (f : FpQuotient) : Bool :=
  Quotient.liftOn f FloatBits.fake_sign (by
    intro a b h
    cases h with
    | inl h =>
      subst h
      simp only [FloatBits.sign, true_and]
    | inr h =>
      unfold FloatBits.fake_sign
      simp only [h, ↓reduceIte]
  )

def FpQuotient.fake_toBitsTriple [FloatFormat] (f : FpQuotient) : FloatBitsTriple :=
  Quotient.liftOn f FloatBits.fake_toBitsTriple (by
    intro a b h
    cases h with
    | inl h =>
      subst h
      simp only
    | inr h =>
      unfold FloatBits.fake_toBitsTriple
      split_ifs
      · simp only [BitVec.ofBool_false, BitVec.ofNat_eq_ofNat]
      · simp_all only [and_false]
      · simp_all only [and_true]
      · simp_all only [and_self]
  )


noncomputable
def FpQuotient.choose [FloatFormat] (f : FpQuotient) : FloatBits :=
  @Quotient.out _ FpSetoid f

/-! Get a concrete bit pattern for the float, using a fixed representation for NaN values. -/
def FpQuotient.representative [FloatFormat] (f : FpQuotient) : FloatBits :=
  if f.isNaN then
    -- TODO: Make sure this isn't a signaling NaN
    have nz : BitVec.allOnes FloatFormat.significandBits ≠ 0 := by
      unfold FloatFormat.significandBits
      apply BitVec.allOnes_ne_zero
      have h := FloatFormat.valid_prec
      omega
    FloatBits.NaN false (BitVec.allOnes FloatFormat.significandBits) nz
  else if f.isInfinite then
    FloatBits.infinite f.fake_sign
  else
    let ⟨sign, exponent, significand⟩ := f.fake_toBitsTriple
    FloatBits.mk' sign exponent significand


theorem FpQuotient.mk_fake_toBitsTriple_eq_fake_toBitsTriple [FloatFormat] (f : FloatBits) :
  (FpQuotient.mk f).fake_toBitsTriple = f.fake_toBitsTriple := by
  unfold FpQuotient.mk FpQuotient.fake_toBitsTriple
  rw [@Quotient.liftOn_mk]

theorem FpQuotient.representative_NaN_imp [FloatFormat] (f : FpQuotient) : f.isNaN → f.representative.isNaN := by
  intro h
  unfold FpQuotient.representative
  split_ifs
  simp_rw [FloatBits.isNaN]
  constructor
  <;> unfold FloatBits.NaN
  <;> norm_num
  · unfold FloatBits.isExponentAllOnes
    rw [FloatBits.construct_exponent_eq_BitsTriple]
  · rw [FloatBits.construct_significand_eq_BitsTriple]
    apply BitVec.allOnes_ne_zero
    symm
    exact FloatFormat.significandBits_pos.ne


theorem FpQuotient.mk_isNaN_imp_isNaN [FloatFormat] (f : FloatBits) : (FpQuotient.mk f).isNaN ↔ f.isNaN := by
  unfold FpQuotient.mk FpQuotient.isNaN
  rw [@Quotient.liftOn_mk]

theorem FpQuotient.representative_NaN_imp_NaN [FloatFormat] (f : FpQuotient) : f.representative.isNaN → f.isNaN := by
  intro h
  unfold FpQuotient.representative at h
  split_ifs at h
  · trivial
  · have := FloatBits.isInfinite_notNaN _ (FloatBits.infinite_isInfinite f.fake_sign)
    contradiction
  · simp at h
    unfold FpQuotient.fake_toBitsTriple at h
    rw [← @Quotient.out_eq _ FpSetoid f, @Quotient.liftOn_mk] at h
    unfold FloatBits.fake_toBitsTriple at h
    split_ifs at h
    · have := (FpQuotient.mk_isNaN_imp_isNaN (@Quotient.out _ FpSetoid f)).mpr (by assumption)
      unfold FpQuotient.mk at this
      rw [@Quotient.out_eq] at this
      trivial
    · have := FloatBits.appendToBitsTriple_eq (@Quotient.out _ FpSetoid f).toBitsTriple (@Quotient.out _ FpSetoid f)
      rw [← @Quotient.out_eq _ FpSetoid f]
      apply (FpQuotient.mk_isNaN_imp_isNaN _).mpr
      rw [← this] at h
      trivial
      rfl

@[simp]
theorem FpQuotient.representative_NaN_iff [FloatFormat] (f : FpQuotient) : f.isNaN ↔ f.representative.isNaN := ⟨FpQuotient.representative_NaN_imp _, FpQuotient.representative_NaN_imp_NaN _⟩

theorem FpQuotient.mk_isInfinite_imp_mk_isInfinite [FloatFormat] (f : FloatBits) : (FpQuotient.mk f).isInfinite ↔ f.isInfinite := by
  unfold FpQuotient.mk FpQuotient.isInfinite
  rw [@Quotient.liftOn_mk]

theorem FpQuotient.mk_isFinite_imp_mk_isFinite [FloatFormat] (f : FloatBits) : (FpQuotient.mk f).isFinite → f.isFinite := by
  unfold FpQuotient.mk FpQuotient.isFinite
  rw [@Quotient.liftOn_mk]
  intro h
  exact h

theorem FpQuotient.mk_fake_sign_eq_fake_sign [FloatFormat] (f : FloatBits) : (FpQuotient.mk f).fake_sign = f.fake_sign := by
  unfold FpQuotient.mk FpQuotient.fake_sign
  rw [@Quotient.liftOn_mk]

theorem FpQuotient.fake_toBitsTriple_eq_toBitsTriple [FloatFormat] :
  ∀ (f : FpQuotient), f.fake_toBitsTriple = f.representative.fake_toBitsTriple := by
  apply Quotient.ind
  intro a
  unfold fake_toBitsTriple
  rw [@Quotient.liftOn_mk _ _ FpSetoid]
  unfold FloatBits.fake_toBitsTriple
  if hn : a.isNaN then
    split_ifs
    · rfl
    · have := FpQuotient.representative_NaN_imp (FpQuotient.mk a) (by assumption)
      contradiction
  else if hi : a.isInfinite then
    split_ifs with c1
    · have := (FpQuotient.representative_NaN_iff _).mpr c1
      contradiction
    · unfold FpQuotient.representative
      split_ifs with c2 c3
      · contradiction
      · unfold FloatBits.infinite FpQuotient.fake_sign FloatBits.fake_sign
        rw [@Quotient.liftOn_mk]
        unfold FloatBits.isInfinite at hi
        simp_all only [Quotient.lift_mk, not_false_eq_true, BitVec.ofNat_eq_ofNat,
          FloatBits.isInfinite_notNaN, ite_false, FloatBitsTriple.mk.injEq]
        rw [FloatBits.construct_sign_eq_BitsTriple, FloatBits.construct_exponent_eq_BitsTriple, FloatBits.construct_significand_eq_BitsTriple, FloatBits.sign]
        split_ands
        · cases BitVec.one_or a.toBitsTriple.sign
          · simp_all only []
            rfl
          · simp_all only [BitVec.ofNat_eq_ofNat, beq_self_eq_true, BitVec.ofBool_true]
        · rfl
        · rfl
      · contradiction
  else
    have hf := FloatBits.cases a
    simp_rw [hn, hi, false_or] at hf
    split_ifs with c1
    · have := (FpQuotient.representative_NaN_iff _).mpr c1
      contradiction
    · norm_num
      split_ands
      all_goals {
        unfold representative
        split_ifs
        · contradiction
        · contradiction
        · rw [mk_fake_toBitsTriple_eq_fake_toBitsTriple]
          -- TODO: is there a better way to write this?
          try rw [FloatBits.construct_sign_eq_BitsTriple]
          try rw [FloatBits.construct_exponent_eq_BitsTriple]
          try rw [FloatBits.construct_significand_eq_BitsTriple]
          unfold FloatBits.fake_toBitsTriple
          split_ifs
          rfl
      }

theorem FpQuotient.isNaN_eq [FloatFormat] (f g : FpQuotient) (hf : f.isNaN) (hg : g.isNaN) : f = g := by
  have hof := @Quotient.out_eq _ FpSetoid f
  have hog := @Quotient.out_eq _ FpSetoid g
  rw [← hof, ← hog]
  apply Quotient.eq_rel.mpr
  unfold Setoid.Rel Setoid.r FpSetoid FpEquiv
  whnf
  right

  rw [← hof] at hf
  rw [← hog] at hg
  have hf' := (FpQuotient.mk_isNaN_imp_isNaN (@Quotient.out _ FpSetoid f)).mp hf
  have hg' := (FpQuotient.mk_isNaN_imp_isNaN (@Quotient.out _ FpSetoid g)).mp hg
  exact ⟨hf', hg'⟩




theorem FpQuotient.representative_eq [FloatFormat] (f : FpQuotient) : f = ⟦FpQuotient.representative f⟧ := by
  unfold FpQuotient.representative
  rw [← @Quotient.out_eq _ FpSetoid f]
  split_ifs with c1 c2
  · apply Quotient.eq_rel.mpr
    unfold Setoid.Rel Setoid.r FpSetoid FpEquiv
    whnf
    right
    constructor
    · apply (FpQuotient.mk_isNaN_imp_isNaN _).mp
      unfold FpQuotient.mk
      exact c1
    · apply FloatBits.NaN_isNaN
  · apply Quotient.eq_rel.mpr
    unfold Setoid.Rel Setoid.r FpSetoid FpEquiv
    whnf
    left
    unfold FpQuotient.isInfinite at c2
    rw [@Quotient.liftOn_mk] at c2
    unfold FloatBits.infinite
    norm_num
    apply (FloatBits.ext_triple' _ _).mpr
    split_ands
    · rw [FloatBits.construct_sign_eq_BitsTriple]
      unfold fake_sign FloatBits.fake_sign
      rw [← @Quotient.out_eq _ FpSetoid f, @Quotient.liftOn_mk]
      split_ifs
      · simp_all only [Quotient.out_eq, representative_NaN_iff, FloatBits.isNaN_notInfinite]
      · unfold FloatBits.sign
        cases BitVec.one_or (@Quotient.out _ FpSetoid f).toBitsTriple.sign
        · simp_all only [Quotient.out_eq, representative_NaN_iff, FloatBits.isInfinite_notNaN, not_false_eq_true, BitVec.ofNat_eq_ofNat]
          rfl
        · simp_all only [Quotient.out_eq, representative_NaN_iff, FloatBits.isInfinite_notNaN, not_false_eq_true, BitVec.ofNat_eq_ofNat]
          rfl
    · rw [FloatBits.construct_exponent_eq_BitsTriple]
      unfold FloatBits.isInfinite at c2
      simp_all only [Quotient.out_eq, representative_NaN_iff]
    · rw [FloatBits.construct_significand_eq_BitsTriple]
      unfold FloatBits.isInfinite at c2
      simp_all only [Quotient.out_eq, representative_NaN_iff, BitVec.ofNat_eq_ofNat]
  · apply Quotient.eq_rel.mpr
    unfold Setoid.Rel Setoid.r FpSetoid FpEquiv
    whnf
    left
    unfold fake_toBitsTriple FloatBits.fake_toBitsTriple
    rw [@Quotient.liftOn_mk]
    apply (FloatBits.ext_triple' _ _).mpr
    split_ifs with c3
    · have := (FpQuotient.mk_isNaN_imp_isNaN _).mpr c3
      unfold FpQuotient.mk at this
      rw [@Quotient.out_eq _ FpSetoid f] at this
      contradiction
    · rw [FloatBits.construct_sign_eq_BitsTriple, FloatBits.construct_exponent_eq_BitsTriple, FloatBits.construct_significand_eq_BitsTriple]
      split_ands <;> rfl

end Fp
