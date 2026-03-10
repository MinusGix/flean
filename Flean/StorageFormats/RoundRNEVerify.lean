import Flean.StorageFormats.FromFp
import Flean.Rounding.ModeClass

/-!
# RoundRNE Verification

Links the bitwise `StorageFp.roundRNE` implementation to the project's canonical
rounding infrastructure (`policyShouldRoundUp .nearestEven`).
-/

namespace StorageFp

private theorem and_one_eq_mod_two (x : ℕ) : x &&& 1 = x % 2 := by
  rw [Nat.and_comm]; exact Nat.one_and_eq_mod_two x

/-- The bitwise RNE conditional structure (halfBit/lower) is equivalent to the
    arithmetic comparison structure (r vs half). -/
private theorem rne_cases_eq (q halfBit lower half r : ℕ)
    (hr : r = lower + half * halfBit) (hllt : lower < half)
    (hhb : halfBit = 0 ∨ halfBit = 1) :
    (if halfBit = 1 then
      if lower ≠ 0 then q + 1
      else if q % 2 = 1 then q + 1 else q
    else q) =
    (if r > half then q + 1
     else if r < half then q
     else if q % 2 ≠ 0 then q + 1 else q) := by
  rcases hhb with hb0 | hb1
  · -- halfBit = 0: r = lower < half
    subst hb0
    rw [if_neg (show ¬((0 : ℕ) = 1) from by omega)]
    have hr_lt : r < half := by omega
    rw [if_neg (show ¬(r > half) from by omega), if_pos hr_lt]
  · -- halfBit = 1: r ≥ half
    subst hb1
    simp only [ite_true]
    by_cases hlower0 : lower = 0
    · -- Exact tie: r = half
      rw [if_neg (show ¬(lower ≠ 0) from not_not.mpr hlower0)]
      rw [if_neg (show ¬(r > half) from by omega), if_neg (show ¬(r < half) from by omega)]
      -- Both sides check q parity: q % 2 = 1 ↔ q % 2 ≠ 0
      have : (q % 2 = 1) = (q % 2 ≠ 0) := propext ⟨fun h => by omega, fun h => by omega⟩
      simp only [this]
    · -- Above halfway: r > half
      rw [if_pos hlower0, if_pos (show r > half from by omega)]

/-- `roundRNE` expressed purely in terms of division and modulo. -/
theorem roundRNE_eq_arith (mag shift : ℕ) (hshift : 0 < shift) :
    roundRNE mag shift =
      let q := mag / 2 ^ shift
      let r := mag % 2 ^ shift
      let half := 2 ^ (shift - 1)
      if r > half then q + 1
      else if r < half then q
      else if q % 2 ≠ 0 then q + 1
      else q := by
  unfold roundRNE
  simp only [show shift ≠ 0 from by omega, ↓reduceIte,
    Nat.shiftRight_eq_div_pow, and_one_eq_mod_two, Nat.and_two_pow_sub_one_eq_mod]
  apply rne_cases_eq
  · have := @Nat.mod_pow_succ mag 2 (shift - 1)
    simp only [show shift - 1 + 1 = shift from by omega] at this
    exact this
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact Nat.mod_two_eq_zero_or_one _

/-- `roundRNE` agrees with `policyShouldRoundUp .nearestEven`. -/
theorem roundRNE_eq_policyShouldRoundUp (mag shift : ℕ) (hshift : 0 < shift) :
    roundRNE mag shift =
      let q := mag / 2 ^ shift
      let r := mag % 2 ^ shift
      if policyShouldRoundUp .nearestEven false q r shift then q + 1 else q := by
  rw [roundRNE_eq_arith mag shift hshift]
  simp only [policyShouldRoundUp]
  have hhalf_pos : 0 < 2 ^ (shift - 1) := Nat.two_pow_pos _
  set r := mag % 2 ^ shift
  set q := mag / 2 ^ shift
  set half := 2 ^ (shift - 1)
  by_cases hr0 : r = 0
  · rw [if_neg (show ¬(r > half) from by omega), if_pos (show r < half from by omega)]
    simp only [hr0, ↓reduceIte, Bool.false_eq_true, ite_false]
  · simp only [hr0, ↓reduceIte]
    split_ifs <;> simp_all <;> omega

/-- The `nearestEven` policy is sign-independent. -/
theorem policyShouldRoundUp_nearestEven_sign_indep (s₁ s₂ : Bool) (q r shift : ℕ) :
    policyShouldRoundUp .nearestEven s₁ q r shift =
    policyShouldRoundUp .nearestEven s₂ q r shift := by
  simp [policyShouldRoundUp]

@[simp]
theorem roundRNE_zero_shift (mag : ℕ) : roundRNE mag 0 = mag := by
  unfold roundRNE; simp

end StorageFp
