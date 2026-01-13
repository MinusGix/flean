import Mathlib.Tactic.Ring
import Mathlib.Tactic.Cases
import Flean.ENNRat.Operations

open Set NNRat

namespace ENNRat

noncomputable section Inv

variable {a b c d : ℚ≥0∞} {r p q : ℚ≥0}

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

@[simp] theorem inv_zero : (0 : ℚ≥0∞)⁻¹ = ∞ := by
  unfold_projs
  rw [ENNRat.inv.eq_def, ← WithTop.some_eq_coe]
  simp_all only [Nat.cast_zero, some_eq_coe, none_eq_top]
  rfl

@[simp] theorem inv_top : ∞⁻¹ = 0 := by
  unfold_projs
  simp_all only [Nat.cast_zero, some_eq_coe', zero_eq_coe]
  rfl

theorem coe_inv_le : (↑r⁻¹ : ℚ≥0∞) ≤ (↑r)⁻¹ := by
  -- TODO: proof needs to be updated for new Lean/mathlib API
  sorry
@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℚ≥0∞) = (↑r)⁻¹ := by
  apply coe_inv_le.antisymm
  -- simp [ENNRat.ofNNRat_eq_NNRatCast, ← coe_mul, mul_inv_cancel₀ hr, coe_one]
  sorry

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℚ≥0) : ℚ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℚ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

lemma coe_div_le : ↑(p / r) ≤ (p / r : ℚ≥0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using mul_le_mul_left' coe_inv_le _

theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]

instance : DivInvOneMonoid ℚ≥0∞ :=
  { inferInstanceAs (DivInvMonoid ℚ≥0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

protected theorem inv_pow : ∀ {a : ℚ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℚ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℚ≥0 using ht
  norm_cast at h0; norm_cast
  -- exact mul_inv_cancel₀ h0
  unfold_projs
  sorry

protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNRat.mul_inv_cancel h0 ht

/-- See `ENNRat.inv_mul_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma inv_mul_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNRat.inv_mul_cancel, *]

/-- See `ENNRat.inv_mul_cancel_left'` for a stronger version. -/
protected lemma inv_mul_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a⁻¹ * (a * b) = b :=
  ENNRat.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNRat.mul_inv_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma mul_inv_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNRat.mul_inv_cancel, *]

/-- See `ENNRat.mul_inv_cancel_left'` for a stronger version. -/
protected lemma mul_inv_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (a⁻¹ * b) = b :=
  ENNRat.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNRat.mul_inv_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma mul_inv_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNRat.mul_inv_cancel, *]

/-- See `ENNRat.mul_inv_cancel_right'` for a stronger version. -/
protected lemma mul_inv_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b * b⁻¹ = a :=
  ENNRat.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNRat.inv_mul_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma inv_mul_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNRat.inv_mul_cancel, *]

/-- See `ENNRat.inv_mul_cancel_right'` for a stronger version. -/
protected lemma inv_mul_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b⁻¹ * b = a :=
  ENNRat.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNRat.mul_div_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma mul_div_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b / b = a := ENNRat.mul_inv_cancel_right' hb₀ hb

/-- See `ENNRat.mul_div_cancel_right'` for a stronger version. -/
protected lemma mul_div_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b / b = a :=
  ENNRat.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNRat.div_mul_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma div_mul_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : b / a * a = b :=
  ENNRat.inv_mul_cancel_right' ha₀ ha

/-- See `ENNRat.div_mul_cancel'` for a stronger version. -/
protected lemma div_mul_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : b / a * a = b :=
  ENNRat.div_mul_cancel' (by simp [ha₀]) (by simp [ha])

/-- See `ENNRat.mul_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma mul_div_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : a * (b / a) = b := by
  rw [mul_comm, ENNRat.div_mul_cancel' ha₀ ha]

/-- See `ENNRat.mul_div_cancel'` for a stronger version. -/
protected lemma mul_div_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (b / a) = b :=
  ENNRat.mul_div_cancel' (by simp [ha₀]) (by simp [ha])

protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]

protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]

instance : InvolutiveInv ℚ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]

@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNRat.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℚ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

theorem div_lt_top {x y : ℚ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
theorem div_ne_top {x y : ℚ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y ≠ ∞ := (div_lt_top h1 h2).ne

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
  ENNRat.mul_pos ha <| ENNRat.inv_ne_zero.2 hb

protected theorem inv_mul_le_iff {x y z : ℚ≥0∞} (h1 : x ≠ 0) (h2 : x ≠ ∞) :
    x⁻¹ * y ≤ z ↔ y ≤ x * z := by
  rw [← mul_le_mul_left h1 h2, ← mul_assoc, ENNRat.mul_inv_cancel h1 h2, one_mul]

protected theorem mul_inv_le_iff {x y z : ℚ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x * y⁻¹ ≤ z ↔ x ≤ z * y := by
  rw [mul_comm, ENNRat.inv_mul_le_iff h1 h2, mul_comm]

protected theorem div_le_iff {x y z : ℚ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ z * y := by
  rw [div_eq_mul_inv, ENNRat.mul_inv_le_iff h1 h2]

protected theorem div_le_iff' {x y z : ℚ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ y * z := by
  rw [mul_comm, ENNRat.div_le_iff h1 h2]

protected theorem mul_inv {a b : ℚ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction' b with b
  · replace ha : a ≠ 0 := ha.neg_resolve_right rfl
    simp [ha]
  induction' a with a
  · replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl)
    simp [hb]
  by_cases h'a : a = 0
  · simp only [h'a, top_mul, ENNRat.inv_zero, ENNRat.coe_ne_top, zero_mul, Ne,
      not_false_iff, ENNRat.coe_zero, ENNRat.inv_eq_zero]
  by_cases h'b : b = 0
  · simp only [h'b, ENNRat.inv_zero, ENNRat.coe_ne_top, mul_top, Ne, not_false_iff,
      mul_zero, ENNRat.coe_zero, ENNRat.inv_eq_zero]
  rw [← ENNRat.coe_mul, ← ENNRat.coe_inv, ← ENNRat.coe_inv h'a, ← ENNRat.coe_inv h'b, ←
    ENNRat.coe_mul, mul_inv_rev, mul_comm]
  simp [h'a, h'b]

protected theorem inv_div {a b : ℚ≥0∞} (htop : b ≠ ∞ ∨ a ≠ ∞) (hzero : b ≠ 0 ∨ a ≠ 0) :
    (a / b)⁻¹ = b / a := by
  rw [← ENNRat.inv_ne_zero] at htop
  rw [← ENNRat.inv_ne_top] at hzero
  rw [ENNRat.div_eq_inv_mul, ENNRat.div_eq_inv_mul, ENNRat.mul_inv htop hzero, mul_comm, inv_inv]

protected theorem mul_div_mul_left (a b : ℚ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNRat.mul_inv (Or.inl hc) (Or.inl hc'), mul_mul_mul_comm,
    ENNRat.mul_inv_cancel hc hc', one_mul]

protected theorem mul_div_mul_right (a b : ℚ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNRat.mul_inv (Or.inr hc') (Or.inr hc), mul_mul_mul_comm,
    ENNRat.mul_inv_cancel hc hc', mul_one]

protected theorem sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNRat.sub_mul (by simpa using h)

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNRat.inv_ne_zero

theorem inv_strictAnti : StrictAnti (Inv.inv : ℚ≥0∞ → ℚ≥0∞) := by
  intro a b h
  lift a to ℚ≥0 using h.ne_top
  sorry
  -- induction b; · simp [ENNRat.coe_ne_top]
  -- rw [coe_lt_coe] at h
  -- rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  -- rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  -- exact NNRat.inv_lt_inv ha h

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_lt

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNRat.inv_lt_inv a b⁻¹

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNRat.inv_lt_inv a⁻¹ b

@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_le

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNRat.inv_le_inv a b⁻¹

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNRat.inv_le_inv a⁻¹ b

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNRat.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNRat.inv_strictAnti h

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℚ≥0∞` and its `OrderDual` -/
@[simps! apply]
def _root_.OrderIso.invENNRat : ℚ≥0∞ ≃o ℚ≥0∞ᵒᵈ where
  map_rel_iff' := ENNRat.inv_le_inv
  toEquiv := (Equiv.inv ℚ≥0∞).trans OrderDual.toDual

@[simp]
theorem _root_.OrderIso.invENNRat_symm_apply (a : ℚ≥0∞ᵒᵈ) :
    OrderIso.invENNRat.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]

@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne

@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNRat.mul_eq_top]

/-- See `ENNRat.div_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma div_div_cancel' (h₀ : a = 0 → b = 0) (h₁ : a = ∞ → b = 0) :
    a / (a / b) = b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNRat.div_eq_inv_mul, ENNRat.inv_div (Or.inr ha') (Or.inr ha),
    ENNRat.div_mul_cancel ha ha']

/-- See `ENNRat.div_div_cancel'` for a stronger version. -/
protected lemma div_div_cancel {a b : ℚ≥0∞} (h₀ : a ≠ 0) (h₁ : a ≠ ∞) :
    a / (a / b) = b :=
  ENNRat.div_div_cancel' (by simp [h₀]) (by simp [h₁])

protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
    a ≤ c / b ↔ a * b ≤ c := by
  induction' b with b
  · lift c to ℚ≥0 using ht.neg_resolve_left rfl
    sorry
  · sorry
  --   rw [div_top, nonpos_iff_eq_zero]
  --   rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  -- rcases eq_or_ne b 0 with (rfl | hb)
  -- · have hc : c ≠ 0 := h0.neg_resolve_left rfl
  --   simp [div_zero hc]
  -- · rw [← coe_ne_zero] at hb
  --   rw [← ENNRat.mul_le_mul_right hb coe_ne_top, ENNRat.div_mul_cancel hb coe_ne_top]

protected theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNRat.le_div_iff_mul_le ?_ ?_).symm <;> simpa

protected theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNRat.div_le_iff_le_mul hb0 hbt)

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNRat.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h

@[simp] protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]

@[simp] protected lemma mul_inv_le_one (a : ℚ≥0∞) : a * a⁻¹ ≤ 1 := ENNRat.div_self_le_one
@[simp] protected lemma inv_mul_le_one (a : ℚ≥0∞) : a⁻¹ * a ≤ 1 := by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma mul_inv_ne_top (a : ℚ≥0∞) : a * a⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma inv_mul_ne_top (a : ℚ≥0∞) : a⁻¹ * a ≠ ⊤ := by simp [mul_comm]

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h

protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNRat.le_div_iff_mul_le h0 ht

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNRat.div_le_of_le_mul h

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h

theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]

theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNRat.div_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNRat.le_div_iff_mul_le] <;>
    · right
      simp

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNRat.inv_le_inv.mpr hdc)

@[gcongr] protected theorem div_le_div_left (h : a ≤ b) (c : ℚ≥0∞) : c / b ≤ c / a :=
  ENNRat.div_le_div le_rfl h

@[gcongr] protected theorem div_le_div_right (h : a ≤ b) (c : ℚ≥0∞) : a / c ≤ b / c :=
  ENNRat.div_le_div h le_rfl

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNRat.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

theorem mul_le_iff_le_inv {a b r : ℚ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNRat.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, ENNRat.mul_inv_cancel hr₀ hr₁,
    one_mul]

protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹

protected theorem div_add_div_same {a b c : ℚ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNRat.add_div.symm

protected theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  ENNRat.mul_inv_cancel h0 hI

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl

theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNRat.mul_div_cancel ha ha'], fun h => by
    rw [← h, mul_div_assoc, ENNRat.mul_div_cancel ha ha']⟩

protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]

theorem div_eq_one_iff {a b : ℚ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNRat.div_self hb₀ hb₁⟩

theorem inv_two_add_inv_two : (2 : ℚ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNRat.div_self two_ne_zero ofNat_ne_top]

theorem inv_three_add_inv_three : (3 : ℚ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [← ENNRat.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]
protected theorem add_halves (a : ℚ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
theorem add_thirds (a : ℚ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]

@[simp] theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]

protected lemma div_ne_zero : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ ∞ := by
  rw [← pos_iff_ne_zero, div_pos_iff]

protected lemma div_mul (a : ℚ≥0∞) (h0 : b ≠ 0 ∨ c ≠ 0) (htop : b ≠ ∞ ∨ c ≠ ∞) :
    a / b * c = a / (b / c) := by
  simp only [div_eq_mul_inv]
  rw [ENNRat.mul_inv, inv_inv]
  · ring
  · simpa
  · simpa

protected lemma mul_div_mul_comm (hc : c ≠ 0 ∨ d ≠ ∞) (hd : c ≠ ∞ ∨ d ≠ 0) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNRat.mul_inv hc hd]
  ring

protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 :=
  ENNRat.div_pos h ofNat_ne_top

protected theorem one_half_lt_one : (2⁻¹ : ℚ≥0∞) < 1 :=
  ENNRat.inv_lt_one.2 <| one_lt_two

-- protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
--   lift a to ℚ≥0 using ht
--   rw [ENNRat.ofNNRat_eq_NNRatCast, coe_ne_zero] at hz
--   rw [← coe_two, ENNRat.ofNNRat_eq_NNRatCast, ← coe_div, coe_lt_coe]
--   exacts [NNRat.half_lt_self hz, two_ne_zero' _]

protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNRat.add_halves _

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := ENNRat.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]
theorem one_sub_inv_two : (1 : ℚ≥0∞) - 2⁻¹ = 2⁻¹ := by
  rw [← one_div, sub_half one_ne_top]

/-- The birational order isomorphism between `ℚ≥0∞` and the unit interval `Set.Iic (1 : ℚ≥0∞)`. -/
@[simps! apply_coe]
def orderIsoIicOneBirational : ℚ≥0∞ ≃o Iic (1 : ℚ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNRat.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNRat.inv_lt_inv, ENNRat.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℚ≥0∞) ≤ x.1⁻¹ := ENNRat.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℚ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl

-- /-- Order isomorphism between an initial interval in `ℚ≥0∞` and an initial interval in `ℚ≥0`. -/
-- @[simps! apply_coe]
-- def orderIsoIicCoe (a : ℚ≥0) : Iic (a : ℚ≥0∞) ≃o Iic a :=
--   OrderIso.symm
--     { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
--       invFun := fun x => ⟨ENNRat.toNNRat x, coe_le_coe.1 <| coe_toNNRat_le_self.trans x.2⟩
--       left_inv := fun _ => Subtype.ext <| toNNRat_coe _
--       right_inv := fun x => Subtype.ext <| coe_toNNRat (ne_top_of_le_ne_top coe_ne_top x.2)
--       map_rel_iff' := fun {_ _} => by
--         simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

-- @[simp]
-- theorem orderIsoIicCoe_symm_apply_coe (a : ℚ≥0) (b : Iic a) :
--     ((orderIsoIicCoe a).symm b : ℚ≥0∞) = b :=
--   rfl

-- /-- An order isomorphism between the extended nonnegative Rat numbers and the unit interval. -/
-- def orderIsoUnitIntervalBirational : ℚ≥0∞ ≃o Icc (0 : ℚ) 1 :=
--   orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNRat.orderIsoIccZeroCoe 1).symm

-- @[simp]
-- theorem orderIsoUnitIntervalBirational_apply_coe (x : ℚ≥0∞) :
--     (orderIsoUnitIntervalBirational x : ℚ) = (x⁻¹ + 1)⁻¹.toRat :=
--   rfl

-- theorem exists_inv_nat_lt {a : ℚ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℚ≥0∞)⁻¹ < a :=
--   inv_inv a ▸ by simp only [ENNRat.inv_lt_inv, ENNRat.exists_nat_gt (inv_ne_top.2 h)]

-- theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
--   let ⟨n, hn⟩ := ENNRat.exists_nat_gt (div_lt_top hb ha).ne
--   ⟨n, Nat.cast_pos.1 ((zero_le _).trans_lt hn), by
--     rwa [← ENNRat.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩

-- theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
--   (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

-- theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
--     ∃ n > 0, ((n : ℕ) : ℚ≥0∞)⁻¹ * a < b := by
--   rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
--   use n, npos
--   rw [← ENNRat.div_eq_inv_mul]
--   exact div_lt_of_lt_mul' hn

-- theorem exists_nnRat_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℚ≥0) * a < b := by
--   rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
--   use (n : ℚ≥0)⁻¹
--   simp [*, npos.ne']

-- theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
--   rcases exists_inv_nat_lt ha with ⟨n, hn⟩
--   refine ⟨n, lt_trans ?_ hn⟩
--   rw [← ENNRat.inv_pow, ENNRat.inv_lt_inv]
--   norm_cast
--   exact n.lt_two_pow_self

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℚ≥0∞) = (r : ℚ≥0∞) ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_coe, coe_pow, zpow_natCast]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · simpa using ENNRat.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNRat.inv_pos, false_and,
      not_false_eq_true]

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · simpa using ENNRat.pow_lt_top h'a.lt_top
  · simp only [ENNRat.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma zpow_ne_top {a : ℚ≥0∞} (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n ≠ ∞ :=
  (ENNRat.zpow_lt_top ha h'a n).ne

-- theorem exists_mem_Ico_zpow {x y : ℚ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
--     ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
--   lift x to ℚ≥0 using h'x
--   lift y to ℚ≥0 using h'y
--   have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
--   obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
--     refine NNRat.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
--     simpa only [Ne, coe_eq_zero] using hx
--   refine ⟨n, ?_, ?_⟩
--   · rwa [← ENNRat.coe_zpow A, ENNRat.coe_le_coe]
--   · rwa [← ENNRat.coe_zpow A, ENNRat.coe_lt_coe]

-- theorem exists_mem_Ioc_zpow {x y : ℚ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
--     ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
--   lift x to ℚ≥0 using h'x
--   lift y to ℚ≥0 using h'y
--   have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
--   obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
--     refine NNRat.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
--     simpa only [Ne, coe_eq_zero] using hx
--   refine ⟨n, ?_, ?_⟩
--   · rwa [← ENNRat.coe_zpow A, ENNRat.coe_lt_coe]
--   · rwa [← ENNRat.coe_zpow A, ENNRat.coe_le_coe]

-- theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℚ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
--     Ioo (0 : ℚ≥0∞) (∞ : ℚ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
--   ext x
--   simp only [mem_iUnion, mem_Ioo, mem_Ico]
--   constructor
--   · rintro ⟨hx, h'x⟩
--     exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
--   · rintro ⟨n, hn, h'n⟩
--     constructor
--     · apply lt_of_lt_of_le _ hn
--       exact ENNRat.zpow_pos (zero_lt_one.trans hy).ne' h'y _
--     · apply lt_trans h'n _
--       exact ENNRat.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
theorem zpow_le_of_le {x : ℚ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_natCast]
    refine (ENNRat.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNRat.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using h

theorem monotone_zpow {x : ℚ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℚ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h

protected theorem zpow_add {x : ℚ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℚ≥0 using h'x
  sorry
  -- replace hx : x ≠ 0 := by simpa only [Ne, coe_eq_zero] using hx
  -- simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]

protected theorem zpow_neg {x : ℚ≥0∞} (x_ne_zero : x ≠ 0) (x_ne_top : x ≠ ⊤) (m : ℤ) :
    x ^ (-m) = (x ^ m)⁻¹ :=
  ENNRat.eq_inv_of_mul_eq_one_left (by simp [← ENNRat.zpow_add x_ne_zero x_ne_top])

protected theorem zpow_sub {x : ℚ≥0∞} (x_ne_zero : x ≠ 0) (x_ne_top : x ≠ ⊤) (m n : ℤ) :
    x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ := by
  rw [sub_eq_add_neg, ENNRat.zpow_add x_ne_zero x_ne_top, ENNRat.zpow_neg x_ne_zero x_ne_top n]

lemma isUnit_iff : IsUnit a ↔ a ≠ 0 ∧ a ≠ ∞ := by
  refine ⟨fun ha ↦ ⟨ha.ne_zero, ?_⟩,
    fun ha ↦ ⟨⟨a, a⁻¹, ENNRat.mul_inv_cancel ha.1 ha.2, ENNRat.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  norm_cast at this
  simp [mul_inv_cancel] at this

/-- Left multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulLeftOrderIso (a : ℚ≥0∞) (ha : IsUnit a) : ℚ≥0∞ ≃o ℚ≥0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNRat.mul_le_mul_left, ha.ne_zero, (isUnit_iff.1 ha).2]

/-- Right multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulRightOrderIso (a : ℚ≥0∞) (ha : IsUnit a) : ℚ≥0∞ ≃o ℚ≥0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNRat.mul_le_mul_right, ha.ne_zero, (isUnit_iff.1 ha).2]

variable {ι κ : Sort*} {f g : ι → ℚ≥0∞} {s : Set ℚ≥0∞} {a : ℚ≥0∞}

theorem ofRat_inv_of_pos {x : ℚ} (hx : 0 < x) : ENNRat.ofRat x⁻¹ = (ENNRat.ofRat x)⁻¹ := by
  rw [ENNRat.ofRat, ENNRat.ofRat, ← @coe_inv (Rat.toNNRat x) (by simp [hx]), coe_inj,
    ← Rat.toNNRat_inv]

theorem ofRat_div_of_pos {x y : ℚ} (hy : 0 < y) :
    ENNRat.ofRat (x / y) = ENNRat.ofRat x / ENNRat.ofRat y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ofRat_mul' (inv_nonneg.2 hy.le), ofRat_inv_of_pos hy]

@[simp] theorem toNNRat_inv (a : ℚ≥0∞) : a⁻¹.toNNRat = a.toNNRat⁻¹ := by
  induction' a with a; · simp
  rcases eq_or_ne a 0 with (rfl | ha); · simp
  rw [← coe_inv ha, toNNRat_coe, toNNRat_coe]

@[simp] theorem toNNRat_div (a b : ℚ≥0∞) : (a / b).toNNRat = a.toNNRat / b.toNNRat := by
  rw [div_eq_mul_inv, toNNRat_mul, toNNRat_inv, div_eq_mul_inv]

@[simp] theorem toRat_inv (a : ℚ≥0∞) : a⁻¹.toRat = a.toRat⁻¹ := by
  simp only [ENNRat.toRat, toNNRat_inv, NNRat.coe_inv]

@[simp] theorem toRat_div (a b : ℚ≥0∞) : (a / b).toRat = a.toRat / b.toRat := by
  -- rw [div_eq_mul_inv, toRat_mul, toRat_inv, div_eq_mul_inv]
  sorry

end Inv
end ENNRat
